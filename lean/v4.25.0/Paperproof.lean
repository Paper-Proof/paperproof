-- The extension injects this file into the user's Lean file too, see /extension/src/services/noInstall/injection.ts
import Lean
import Lean.Meta.Basic
import Lean.Meta.CollectMVars
import Lean.Server.Requests


open Lean Elab

namespace Paperproof.Services

/--
  InfoTree has a lot of non-user-written intermediate `TacticInfo`s, this function returns `none` for those.
  @EXAMPLES
  `tInfo.stx`               //=> `(Tactic.tacticSeq1Indented [(Tactic.exact "exact" (Term.proj ab "." (fieldIdx "2")))])`
  `tInfo.stx.getSubstring?` //=> `(some (exact ab.2 ))`
  `tInfo.stx`               //=> `(Tactic.rotateRight "rotate_right" []) -- (that's not actually present in our proof)`
  `tInfo.stx.getSubstring?` //=> `None`
-/
public def getTacticSubstring (tInfo : TacticInfo) : Option Substring :=
  match tInfo.stx.getSubstring? with
  | .some substring => substring
  | .none => none

end Paperproof.Services



open Lean Elab Server

namespace Paperproof.Services

public structure ArgumentInfo where
  name : String
  type : String
  deriving Inhabited, FromJson, ToJson

structure DeclarationInfo where
  name : Name
  declarationType : String  -- "theorem", "lemma", "definition", "axiom", etc.
  body : Option String  -- definition body if applicable
  deriving Inhabited, FromJson, ToJson

instance : BEq DeclarationInfo where
  beq a b := a.name == b.name

instance : Hashable DeclarationInfo where
  hash a := hash a.name

public structure TheoremSignature where
  name              : String
  instanceArgs      : List ArgumentInfo := [] -- []
  implicitArgs      : List ArgumentInfo := [] -- {}
  explicitArgs      : List ArgumentInfo := [] -- ()
  type              : String := ""            -- return type
  declarationType   : String := ""            -- declaration type
  body              : Option String := none   -- definition body if applicable
  deriving Inhabited, FromJson, ToJson

partial def getIds : Syntax → NameSet
  | .node _ _ args => (args.map getIds).foldl (·.append ·) {}
  | .ident _ _ nm _ => NameSet.empty.insert nm
  | _ => {}

def getAllArgsWithTypes (expr : Expr) : MetaM (List ArgumentInfo × List ArgumentInfo × List ArgumentInfo × String) := do
  Meta.forallTelescope expr fun args body => do
    let mut lctx := LocalContext.empty
    for arg in args do
      let decl ← arg.fvarId!.getDecl
      lctx := lctx.addDecl decl
    
    let ppCtx : PPContext := { 
      env := ← getEnv, 
      mctx := ← getMCtx, 
      lctx, 
      opts := (← getOptions).setBool `pp.fullNames true 
    }
    
    let mut instanceArgs := []
    let mut implicitArgs := []
    let mut explicitArgs := []
    
    for arg in args do
      let decl ← arg.fvarId!.getDecl
      let typeStr ← ppExprWithInfos ppCtx decl.type
      let argInfo := { name := decl.userName.toString, type := typeStr.fmt.pretty : ArgumentInfo }
      
      match decl.binderInfo with
      | BinderInfo.instImplicit => instanceArgs := instanceArgs ++ [argInfo]
      | BinderInfo.implicit => implicitArgs := implicitArgs ++ [argInfo]
      | BinderInfo.strictImplicit => implicitArgs := implicitArgs ++ [argInfo]
      | BinderInfo.default => explicitArgs := explicitArgs ++ [argInfo]
    
    let bodyStr ← ppExprWithInfos ppCtx body
    return (instanceArgs, implicitArgs, explicitArgs, bodyStr.fmt.pretty)


/-- Check if a substring position is within a given range -/
def isInRange (substr : Substring) (startPos stopPos : String.Pos.Raw) : Bool :=
  substr.startPos >= startPos && substr.stopPos <= stopPos

/-- Get declaration type string from ConstantInfo -/
def getDeclarationType (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "def"
  | .thmInfo _    => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _   => "constructor"
  | .recInfo _    => "recursor"

/-- Process a declaration and extract all relevant info (type, args, body) -/
def processDeclaration (name : Name) (ctx : ContextInfo) (goalDecl : MetavarDecl) : MetaM (Option TheoremSignature) := do
  let constInfo ← getConstInfo name
  let declType := getDeclarationType constInfo
  
  -- Only process theorems, axioms, and definitions
  unless (declType == "theorem" || declType == "axiom" || declType == "def") do
    return none
  
  let ppCtx := { (ctx.toPPContext (goalDecl.lctx |>.sanitizeNames.run' {options := {}})) with 
    opts := (ctx.toPPContext goalDecl.lctx).opts.setBool `pp.fullNames true }
  
  -- Get the name with full qualification
  let nameStr ← ppExprWithInfos ppCtx (mkConst constInfo.name)
  
  -- Extract arguments and return type
  let (instanceArgs, implicitArgs, explicitArgs, typeStr) ← getAllArgsWithTypes constInfo.type
  
  -- Only include definition body for "def" declarations
  let declBody ← 
    if declType == "def" then
      match constInfo.value? with
      | some expr => do
        let bodyStr ← ppExprWithInfos ppCtx expr
        pure (some bodyStr.fmt.pretty)
      | none => pure none
    else
      pure none
  
  return some { 
    name := nameStr.fmt.pretty,
    instanceArgs,
    implicitArgs,
    explicitArgs,
    type := typeStr,
    declarationType := declType,
    body := declBody
  }

-- TODO I think now we can remove everything and just leave .const here
/-- Extract theorem name from expression, handling constants, applications, and local variables -/
def extractTheoremName (expr : Expr) (lctx : LocalContext) : Option Name := do
  guard (!expr.isSyntheticSorry)
  -- It's important to use cleanExpr here, otherwise we'll be getting "fvar expected" exceptions sometimes
  let cleanExpr := expr.consumeMData
  match cleanExpr with
  | .const name _ => some name
  | .app .. => expr.getAppFn.consumeMData.constName?
  | .fvar .. => do
    let ldecl ← lctx.findFVar? cleanExpr
    let val ← ldecl.value?
    val.getAppFn.consumeMData.constName?
  | _ => none

/-- Extract theorem names exactly like Lean's hover does - using built-in hover functionality -/
def findTheoremsLikeHover (tree : Elab.InfoTree) (tacticStartPos tacticStopPos : String.Pos.Raw) (ctx : ContextInfo) (goalDecl : MetavarDecl) : MetaM (List TheoremSignature) := do
  let mut theoremNames : NameSet := {}

  -- Sample positions throughout the tactic range (every few characters)
  -- This ensures we catch all identifiers that would show on hover
  let mut currentPos := tacticStartPos
  let step : Nat := 3  -- Check every 3 characters

  while currentPos < tacticStopPos do
    -- Use Lean's actual hover function to find what would show at this position
    if let some infoWithCtx ← tree.hoverableInfoAtM? currentPos then
      -- Extract theorem name from the hover info
      match infoWithCtx.info with
      | .ofTermInfo termInfo =>
        if let some name := extractTheoremName termInfo.expr termInfo.lctx then
          theoremNames := theoremNames.insert name
      | _ => pure ()

    currentPos := ⟨currentPos.byteIdx + step⟩
  
  -- Process each theorem name and filter for relevant declarations
  let theoremSignatures ← theoremNames.toList.filterMapM fun name => do
    let resolvedName ← resolveGlobalConstNoOverloadCore name
    processDeclaration resolvedName ctx goalDecl
  
  pure theoremSignatures


public def GetTheorems (infoTree : InfoTree) (tacticInfo : TacticInfo) (ctx : ContextInfo) : MetaM (List TheoremSignature) := do
  let some goalMVar := tacticInfo.goalsBefore.head?
    | throwError "noGoals"
  let some goalDecl := ctx.mctx.findDecl? goalMVar
    | throwError "noGoalDecl"
  let some tacticSubstring := getTacticSubstring tacticInfo
    | throwError "noTacticSubstring"

  ctx.runMetaM goalDecl.lctx do
    findTheoremsLikeHover infoTree tacticSubstring.startPos tacticSubstring.stopPos ctx goalDecl

end Paperproof.Services



open Lean Elab Server

namespace Paperproof.Services

public structure Hypothesis where
  username : String
  type : String
  value : Option String
  -- unique identifier for the hypothesis, fvarId
  id : String
  isProof : String
  deriving Inhabited, ToJson, FromJson

public structure GoalInfo where
  username : String
  type : String
  hyps : List Hypothesis
  -- unique identifier for the goal, mvarId
  id : MVarId
  deriving Inhabited, ToJson, FromJson

public instance : BEq GoalInfo where
  beq g1 g2 := g1.id == g2.id

public instance : Hashable GoalInfo where
  hash g := hash g.id

public structure ProofStepPosition where
  start: Lsp.Position
  stop: Lsp.Position
  deriving Inhabited, ToJson, FromJson

public structure ProofStep where
  tacticString    : String
  goalBefore      : GoalInfo
  goalsAfter      : List GoalInfo
  tacticDependsOn : List String
  spawnedGoals    : List GoalInfo
  position        : ProofStepPosition
  theorems        : List TheoremSignature
  deriving Inhabited, ToJson, FromJson

def stepGoalsAfter (step : ProofStep) : List GoalInfo := step.goalsAfter ++ step.spawnedGoals

def noInEdgeGoals (allGoals : Std.HashSet GoalInfo) (steps : List ProofStep) : Std.HashSet GoalInfo :=
  -- Some of the orphaned goals might be matched by tactics in sibling subtrees, e.g. for tacticSeq.
  (steps.flatMap stepGoalsAfter).foldl Std.HashSet.erase allGoals

/-
  Instead of doing parsing of what user wrote (it wouldn't work for linarith etc),
  let's do the following.
  We have assigned something to our goal in mctxAfter.
  All the fvars used in these assignments are what was actually used instead of what was in syntax.
-/
def findHypsUsedByTactic (goalId: MVarId) (goalDecl : MetavarDecl) (mctxAfter : MetavarContext) : MetaM (List String) := do
  let some expr := mctxAfter.eAssignment.find? goalId
    | return []

  -- Need to instantiate it to get all fvars
  let fullExpr ← instantiateExprMVars expr
  let fvarIds := (collectFVars {} fullExpr).fvarIds
  let fvars := fvarIds.filterMap goalDecl.lctx.find?
  return fvars.map (fun x => x.fvarId.name.toString) |>.toList

-- This is used to match goalsBefore with goalsAfter to see what was assigned to what
def findMVarsAssigned (goalId : MVarId) (mctxAfter : MetavarContext) : MetaM (List MVarId) := do
  let some expr := mctxAfter.eAssignment.find? goalId
    | return []
  let (_, s) ← (Meta.collectMVars expr).run {}
  return s.result.toList

def mayBeProof (expr : Expr) : MetaM String := do
  let type : Expr ← Lean.Meta.inferType expr
  if ← Meta.isProof expr then
    return "proof"
  if type.isSort then
    return "universe"
  else
    return "data"

public def printGoalInfo (printCtx : ContextInfo) (id : MVarId) : MetaM GoalInfo := do
  let some decl := printCtx.mctx.findDecl? id
    | throwError "goalNotFoundInMctx"
  -- to get tombstones in name ✝ for unreachable hypothesis
  let lctx := decl.lctx |>.sanitizeNames.run' {options := {}}
  let ppContext := printCtx.toPPContext lctx
  let hyps ← lctx.foldrM (init := []) (fun hypDecl acc => do
    if hypDecl.isAuxDecl || hypDecl.isImplementationDetail then
      return acc
    let type ← ppExprWithInfos ppContext hypDecl.type
    let value ← hypDecl.value?.mapM (fun expr => ppExprWithInfos ppContext expr)
    let isProof : String ← printCtx.runMetaM decl.lctx (mayBeProof hypDecl.toExpr)
    return ({
      username := hypDecl.userName.toString,
      type     := type.fmt.pretty,
      value    := value.map (·.fmt.pretty),
      id       := hypDecl.fvarId.name.toString,
      isProof  := isProof
    } : Hypothesis) :: acc)
  return {
    username := decl.userName.toString
    type     := (← ppExprWithInfos ppContext decl.type).fmt.pretty
    hyps     := hyps
    id       := id
  }

-- Returns unassigned goals from the provided list of goals
def getUnassignedGoals (goals : List MVarId) (mctx : MetavarContext) : MetaM (List MVarId) := do
  goals.filterMapM fun id => do
    if let none := mctx.findDecl? id then
      return none
    if mctx.eAssignment.contains id ||
       mctx.dAssignment.contains id then
      return none
    return some id

public structure Result where
  steps : List ProofStep
  allGoals : Std.HashSet GoalInfo

/--
  [Claude comment]

  Tactics like `split_ifs` split one condition at a time - a binary tree of `by_cases` - but
  only the leaves of that tree survive as `goalsAfter`. Drawn as one step with 2ⁿ goals, every
  leaf lists all n new hypotheses, so `h : ‖f x‖ₑ ≤ b` from the first split repeats in half
  of the boxes. The intermediate goals are still in `mctxAfter`, so we recover the tree:
  returns `(node, children)` edges from `root` down to `leaves`. Chains with a single child
  (the `intro` and `simp` steps between two splits) are collapsed to their last goal, which
  is the one that already has the new hypothesis and the simplified target.
-/
partial def splitTreeEdges (mctx : MetavarContext) (root : MVarId) (leaves : List MVarId) : List (MVarId × List MVarId) :=
  let directChildren (m : MVarId) : List MVarId :=
    match mctx.eAssignment.find? m with
    | none   => []
    | some e => (e.collectMVars {}).result.toList.map fun c =>
      match mctx.getDelayedMVarAssignmentCore? c with
      | some d => d.mvarIdPending
      | none   => c
  let rec reaches (m : MVarId) : Bool := leaves.contains m || (directChildren m).any reaches
  let relevantChildren (m : MVarId) : List MVarId := (directChildren m).filter reaches |>.eraseDups
  let rec collapse (m : MVarId) : MVarId :=
    if leaves.contains m then m else
    match relevantChildren m with
    | [c] => collapse c
    | _   => m
  let rec edges (m : MVarId) : List (MVarId × List MVarId) :=
    if leaves.contains m then [] else
    let kids := (relevantChildren m).map collapse
    (m, kids) :: kids.flatMap edges
  -- The root keeps its own id (it's the tactic's `goalBefore`), but takes its children from
  -- the first real split - otherwise a chain right below the root becomes a no-op step
  match edges (collapse root) with
  | (_, kids) :: rest => (root, kids) :: rest
  | []                => []

/--
  [Claude comment]

  We only rebuild the tree when it removes repetition: some new hypothesis is shared by
  several leaves but not by all of them. Otherwise (`constructor`, `rcases h with a | b`, ...)
  the flat `goalBefore → goalsAfter` step is already the right picture.
-/
def hasSharedBranchHyps (mctx : MetavarContext) (root : MVarId) (leaves : List MVarId) : Bool := Id.run do
  let some rootDecl := mctx.findDecl? root | return false
  let leafHyps := leaves.map fun l =>
    (mctx.findDecl? l).map (fun d => d.lctx.getFVarIds.toList.filter (!rootDecl.lctx.contains ·)) |>.getD []
  let allNew := leafHyps.flatten.eraseDups
  return allNew.any fun fvar =>
    let count := leafHyps.countP (·.contains fvar)
    2 ≤ count && count < leaves.length

/--
  [Claude comment]

  The `(goal, children)` edges to draw for one tactic: the recovered split tree when it helps,
  otherwise the single flat edge `root → leaves`. We also fall back to the flat edge if the
  tree isn't a clean tree over exactly `leaves` - better a repetitive picture than a goal
  that silently disappears (or gets drawn twice).
-/
def goalEdges (mctx : MetavarContext) (root : MVarId) (leaves : List MVarId) : List (MVarId × List MVarId) :=
  let flat := [(root, leaves)]
  if !hasSharedBranchHyps mctx root leaves then flat else
  let edges := splitTreeEdges mctx root leaves
  let nodes := edges.map (·.1)
  let reachedLeaves := edges.flatMap (·.2) |>.filter leaves.contains
  let isCleanTree := nodes.eraseDups.length == nodes.length &&
    reachedLeaves.length == leaves.length && leaves.all reachedLeaves.contains
  if isCleanTree then edges else flat

def getGoalsChange (ctx : ContextInfo) (tInfo : TacticInfo) : MetaM (List (List String × GoalInfo × List GoalInfo)) := do
  -- We want to filter out `focus` like tactics which don't do any assignments
  -- therefore we check all goals on whether they were assigned during the tactic
  let goalMVars := tInfo.goalsBefore ++ tInfo.goalsAfter
  -- For printing purposes we always need to use the latest mctx assignments. For example in
  -- have h := by calc
  --  3 ≤ 4 := by trivial
  --  4 ≤ 5 := by trivial
  -- at mctxBefore type of `h` is `?m.260`, but by the time calc is elaborated at mctxAfter
  -- it's known to be `3 ≤ 5`
  let printCtx := {ctx with mctx := tInfo.mctxAfter}
  let mut goalsBefore ← getUnassignedGoals goalMVars tInfo.mctxBefore
  let mut goalsAfter ← getUnassignedGoals goalMVars tInfo.mctxAfter
  let commonGoals := goalsBefore.filter fun g => goalsAfter.contains g
  goalsBefore := goalsBefore.filter (!commonGoals.contains ·)
  goalsAfter :=  goalsAfter.filter (!commonGoals.contains ·)
  -- We need to match them into (goalBefore, goalsAfter) pairs according to assignment.
  let mut result : List (List String × GoalInfo × List GoalInfo) := []
  for goalBefore in goalsBefore do
    if let some goalDecl := tInfo.mctxBefore.findDecl? goalBefore then
      let assignedMVars ← ctx.runMetaM goalDecl.lctx (findMVarsAssigned goalBefore tInfo.mctxAfter)
      let tacticDependsOn ← ctx.runMetaM goalDecl.lctx
          (findHypsUsedByTactic goalBefore goalDecl tInfo.mctxAfter)

      let leaves := goalsAfter.filter assignedMVars.contains
      let edges ← goalEdges tInfo.mctxAfter goalBefore leaves |>.mapM fun (node, kids) => do
        return (
          if node == goalBefore then tacticDependsOn else [],
          ← printGoalInfo printCtx node,
          ← kids.mapM (printGoalInfo printCtx)
        )
      result := edges ++ result
  return result

def prettifySteps (stx : Syntax) (steps : List ProofStep) (tacticString : String) : List ProofStep := Id.run do
  match stx with
  | `(tactic| rw [$_,*] $(_)?)
  | `(tactic| rewrite [$_,*] $(_)?) =>
    let prettify (tStr : String) :=
      let res := tStr.trim.dropRightWhile (· == ',')
      -- rw puts final rfl on the "]" token
      if res == "]" then "rfl" else res
    return steps.map fun a => { a with tacticString := s!"rw [{prettify a.tacticString}]" }
  | `(tactic| intro $_ $_ $_*) =>
    -- intro with 2+ names generates one child TacticInfo per name; merge into a single step
    if steps.isEmpty then return steps
    return [{ steps.head! with
      tacticString        := tacticString,
      goalsAfter          := steps.getLast!.goalsAfter,
      tacticDependsOn     := (steps.flatMap (·.tacticDependsOn)).eraseDups }]
  | _ => return steps

-- Comparator for names, e.g. so that _uniq.34 and _uniq.102 go in the right order.
-- That's not completely right because it doesn't compare prefixes but
-- it's much shorter to write than correct version and serves the purpose.
def nameNumLt (n1 n2 : Name) : Bool :=
  match n1, n2 with
  | .num _ n₁, .num _ n₂ => n₁ < n₂
  | .num _ _,  _ => true
  | _, _ => false

/--
  By default, `.getSubstring()` captures empty lines and comments after the tactic - this function removes them.
-/
def prettifyTacticString (tacticString: String) : String :=
  ((tacticString.splitOn "\n").head?.getD tacticString).trim

def getProofStepPosition (fileMap : FileMap) (tacticSubstring: Substring) : ProofStepPosition := {
  start := Lean.FileMap.utf8PosToLspPos fileMap tacticSubstring.startPos,
  stop  := Lean.FileMap.utf8PosToLspPos fileMap tacticSubstring.stopPos
}

/--
  [Claude comment]

  Tactics like `filter_upwards [h] with y hy` run a synthetic `intro y hy`, which has no source
  substring, so it never reaches `prettifySteps` to have its per-name child steps merged. The
  children whose syntax is user-written (`hy`) would then surface as a dangling step whose
  `goalBefore` has no in-edge (rendered as a stray have box). The enclosing user-written tactic
  already covers this goal change, so we drop these steps together with their goals.
-/
def dropSyntheticIntroSteps (stx : Syntax) (steps : List ProofStep) (allGoals : Std.HashSet GoalInfo)
    : List ProofStep × Std.HashSet GoalInfo :=
  if stx.getKind != ``Lean.Parser.Tactic.intro then (steps, allGoals) else
  ([], (steps.flatMap (fun s => s.goalBefore :: stepGoalsAfter s)).foldl Std.HashSet.erase allGoals)

def parseTacticBody (fileMap : FileMap) (ctx : ContextInfo) (tInfo : TacticInfo) (tacticSubstring : Substring) (steps : List ProofStep) (allGoals : Std.HashSet GoalInfo) (tacticString : String) (theorems : List TheoremSignature) : MetaM Result := do
  let steps := prettifySteps tInfo.stx steps tacticString
  let position := getProofStepPosition fileMap tacticSubstring

  let proofTreeEdges ← getGoalsChange ctx tInfo
  let currentGoals := proofTreeEdges.map (fun ⟨ _, g₁, gs ⟩ => g₁ :: gs)  |>.flatten
  let allGoals := allGoals.insertMany $ currentGoals
  -- It's like tacticDependsOn but unnamed mvars instead of hyps.
  -- Important to sort for have := calc for example, e.g. calc 3 < 4 ... 4 < 5 ...
  let orphanedGoals := currentGoals.foldl Std.HashSet.erase (noInEdgeGoals allGoals steps)
    |>.toArray.insertionSort (nameNumLt ·.id.name ·.id.name) |>.toList

  let newSteps := proofTreeEdges.filterMap fun ⟨ tacticDependsOn, goalBefore, goalsAfter ⟩ =>
    -- Leave only steps which are not handled in the subtree.
    if steps.map (·.goalBefore) |>.elem goalBefore then
      none
    else
      some {
        tacticString,
        goalBefore,
        goalsAfter,
        tacticDependsOn,
        spawnedGoals := orphanedGoals
        position,
        theorems
      }

  return { steps := newSteps ++ steps, allGoals }

public def BetterParser_Tree (fileMap : FileMap) (infoTree : InfoTree) : MetaM (Option Result) :=
  infoTree.visitM (postNode := fun ctx info _ results => do
    -- Remove `Option.none` values from the `results` list (we have them because of the `.visitM` implementation)
    let results : List Result := results.filterMap id
    -- 1. Flatten `ProofStep`s
    let steps : List ProofStep := (results.map (λ result => result.steps)).flatten
    -- 2. Flatten `GoalInfo`s
    let allGoals : Std.HashSet GoalInfo := Std.HashSet.ofList ((results.map (λ result => result.allGoals.toList)).flatten)
    -- 3. Parse tactic
    let .some ctx := info.updateContext? ctx              | panic! "unexpected context node"
    let .ofTacticInfo tInfo := info                       | return { steps, allGoals }
    let .some tacticSubstring := getTacticSubstring tInfo
      | let (steps, allGoals) := dropSyntheticIntroSteps tInfo.stx steps allGoals
        return { steps, allGoals }
    let tacticString := prettifyTacticString (Substring.toString tacticSubstring)
    parseTacticBody fileMap ctx tInfo tacticSubstring steps allGoals tacticString []
  )

public def BetterParser_SingleTactic (fileMap: FileMap) (infoTree: InfoTree) (ctx : ContextInfo) (info : Info) (steps : List ProofStep) (allGoals : Std.HashSet GoalInfo) (forcedTacticString : String) : MetaM Result := do
  -- 1. Parse tactic
  let .some ctx := info.updateContext? ctx               | panic! "unexpected context node"
  let .ofTacticInfo tInfo := info                        | return { steps, allGoals }
  let .some tacticSubstring := getTacticSubstring tInfo  | return { steps, allGoals }
  let tacticString := if forcedTacticString.length > 0
    then forcedTacticString
    else prettifyTacticString (Substring.toString tacticSubstring)
  let theorems ← GetTheorems infoTree tInfo ctx
  parseTacticBody fileMap ctx tInfo tacticSubstring steps allGoals tacticString theorems

end Paperproof.Services

namespace Paperproof

structure TheoremUsedInProof where
  name : String
  kind : String
  signature : String
  deriving Lean.ToJson

open Lean Elab Command Meta in
def findTheoremsUsedInProof (trees : List Lean.Elab.InfoTree) (selfName : Name)
    : MetaM (List TheoremUsedInProof) := do
  let env ← getEnv
  let r ← IO.mkRef ({} : Std.HashSet Name)
  for t in trees do
    t.visitM' (postNode := fun _ info _ => do
      -- keep only identifiers the user wrote, so notation plumbing
      -- (HAdd.hAdd from `+`, OfNat.ofNat from `0`) is dropped
      if let .ofTermInfo ti := info then
        if info.stx.isIdent && info.pos?.isSome then
          let nm? := match ti.expr.consumeMData with
            | .const nm _ => some nm
            | e@(.app ..) => e.getAppFn.consumeMData.constName?
            | _ => none
          if let some nm := nm? then r.modify (·.insert nm)
      pure ())
  let names := (← r.get).toList
  names.filterMapM (fun nm => do
    -- drop self: `selfName` is the short (unqualified) declId, so compare the
    -- last name component against the fully-qualified names found in the env
    if nm == selfName || nm.components.getLast? == selfName.components.getLast? then
      return none
    match env.find? nm with
    | some ci =>
      -- classify by the type, not the constructor: the module system erases
      -- imported proofs, so a theorem is seen here as `.axiomInfo`
      let kind ←
        if (← Meta.isProp ci.type) then pure "theorem"
        else match ci with
          | .defnInfo _ => pure "def"
          | .axiomInfo _ => pure "axiom"
          | _ => pure ""
      if kind == "" then return none
      -- drop type constructors (`Set`, `List`, …): a def whose type ends in a
      -- sort is a type appearing in the goal/hyps, not a lemma the proof uses
      if kind == "def" then
        -- non-reducing: keep the syntactic result type, so `Set α` stays `Set α`
        -- (kept) rather than unfolding to `α → Prop` and looking like a sort
        if (← Meta.forallTelescope ci.type fun _ body => pure body.isSort) then
          return none
      let typeStr := (← Meta.ppExpr ci.type).pretty
      -- for a def the type (e.g. `ℕ → ℕ`) is uninformative; show the body it
      -- unfolds to, since that is what `rw`/`unfold`/`simp only` will expose
      let signature ←
        if kind == "def" then
          match ci with
          | .defnInfo dv =>
            (do
              let bodyStr := (← Meta.ppExpr dv.value).pretty
              pure s!"{typeStr} := {bodyStr}") <|> pure typeStr
          | _ => pure typeStr
        else pure typeStr
      return some { name := nm.toString, kind, signature : TheoremUsedInProof }
    | none => return none)

public structure RpcParams where
  pos : Lean.Lsp.Position
  includeTheorems : Bool
  deriving Lean.FromJson, Lean.ToJson

open Lean Server RequestM in
/-- Accepts a snapshot, and returns the proof in the format that `<Paperproof proof={proof}/>` expects (see https://www.npmjs.com/package/paperproof). -/
public def getProof (snapshot : Snapshots.Snapshot) : RequestM (Option Json) := do
  let fileMap := (← readDoc).meta.text
  let some parsedTree ← RequestM.runTermElabM snapshot (liftM <| Paperproof.Services.BetterParser_Tree fileMap snapshot.infoTree)
    | return none
  if parsedTree.steps.isEmpty then return none
  return toJson parsedTree.steps

-- The RPC runner: called by position, `withWaitFindSnapAtPos` resolves the
-- position to the enclosing proof's snapshot, then we parse its infoTree. Must
-- be `public` or the module system mangles its name and the RPC can't find it.
open Lean Elab Server RequestM in
@[server_rpc_method]
public def getProofAt (params : RpcParams) : RequestM (RequestTask String) :=
  withWaitFindSnapAtPos params.pos fun snap => do
    let fileMap := (← readDoc).meta.text
    let some parsed ← RequestM.runTermElabM snap
        (liftM <| Paperproof.Services.BetterParser_Tree fileMap snap.infoTree)
      | throwThe RequestError ⟨.invalidParams, "noParsedTree"⟩
    let rawId := snap.stx.find? (·.isOfKind ``Lean.Parser.Command.declId)
      |>.map (·[0].getId) |>.getD Name.anonymous
    let thms ← if params.includeTheorems then
        RequestM.runTermElabM snap (liftM <| findTheoremsUsedInProof [snap.infoTree] rawId)
      else pure []
    let out := Lean.Json.mkObj [
      ("name", Lean.toJson rawId.toString),
      ("steps", Lean.toJson parsed.steps),
      ("theorems", Lean.toJson thms)
    ]
    return out.compress

end Paperproof
