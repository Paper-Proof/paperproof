-- Paperproof parser (GetTacticSubstring + GetTheorems + BetterParser) plus the
-- ppMcpGetProof RPC runner, hand-maintained for Lean 4.27. Namespaced
-- PaperproofMcp.Services so it never clashes with a real `import Paperproof`.
import Lean
import Lean.Meta.Basic
import Lean.Meta.CollectMVars
import Lean.Server.Requests
-- Services/GetTacticSubstring.lean


open Lean Elab

namespace PaperproofMcp.Services

/--
  InfoTree has a lot of non-user-written intermediate `TacticInfo`s, this function returns `none` for those.
  @EXAMPLES
  `tInfo.stx`               //=> `(Tactic.tacticSeq1Indented [(Tactic.exact "exact" (Term.proj ab "." (fieldIdx "2")))])`
  `tInfo.stx.getSubstring?` //=> `(some (exact ab.2 ))`
  `tInfo.stx`               //=> `(Tactic.rotateRight "rotate_right" []) -- (that's not actually present in our proof)`
  `tInfo.stx.getSubstring?` //=> `None`
-/
public def getTacticSubstring (tInfo : TacticInfo) : Option Substring.Raw :=
  match tInfo.stx.getSubstring? with
  | .some substring => substring
  | .none => none

end PaperproofMcp.Services
-- Services/GetTheorems.lean



open Lean Elab Server

namespace PaperproofMcp.Services

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
def isInRange (substr : Substring.Raw) (startPos stopPos : String.Pos.Raw) : Bool :=
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

end PaperproofMcp.Services
-- Services/BetterParser.lean



open Lean Elab Server

namespace PaperproofMcp.Services

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
    if let some assignment := mctx.eAssignment.find? id then
      -- [Claude comment] an erroring tactic gets its goal assigned a *synthetic* sorry, which would
      -- otherwise be indistinguishable from the tactic having closed the goal.
      unless assignment.hasSyntheticSorry do
        return none
      return some id
    if mctx.dAssignment.contains id then
      return none
    return some id

public structure Result where
  steps : List ProofStep
  allGoals : Std.HashSet GoalInfo

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

      result := (
        tacticDependsOn,
        ← printGoalInfo printCtx goalBefore,
        ← goalsAfter.filter assignedMVars.contains |>.mapM (printGoalInfo printCtx)
      ) :: result
  return result

/--
  By default, `.getSubstring()` captures empty lines and comments after the tactic - this function removes them.
-/
def prettifyTacticString (tacticString: String) : String :=
  ((tacticString.splitOn "\n").head?.getD tacticString).trimAscii.toString

def lspPos? (fileMap : FileMap) (stx : Syntax) : Option Lsp.Position :=
  stx.getPos?.map (Lean.FileMap.utf8PosToLspPos fileMap)

def isSamePosition (p₁ p₂ : Lsp.Position) : Bool :=
  p₁.line == p₂.line && p₁.character == p₂.character

/--
  Rewriting tactics (`rw`, `rewrite`, `simp_rw`, `nth_rw`, ...) create a separate `TacticInfo` for
  every rewrite rule, and the syntax of such a `TacticInfo` is the rule together with its trailing
  comma. So the steps of `simp_rw [c𝓑, r𝓑]` are named `c𝓑,` and `r𝓑` - here we rename them into
  `simp_rw [c𝓑]` and `simp_rw [r𝓑]`.
  We recognize these steps by their position (a step could also come from a nested proof, as in
  `rw [show a = b from by exact h]` - such steps should keep their own name).
-/
def prettifyRwSteps (fileMap : FileMap) (stx : Syntax) (steps : List ProofStep) : List ProofStep := Id.run do
  let .some ruleSeq := stx.getArgs.find? (·.getKind == ``Lean.Parser.Tactic.rwRuleSeq) | return steps
  -- Everything the user wrote before the "[", e.g. "rw", "simp_rw", "nth_rw 2"
  let .some tacticStart := stx.getPos?                                                 | return steps
  let .some ruleSeqStart := ruleSeq.getPos?                                            | return steps
  let tacticName := prettifyTacticString (Substring.Raw.toString ⟨fileMap.source, tacticStart, ruleSeqStart⟩)

  let ruleStarts := ruleSeq[1].getArgs.filterMap fun rule =>
    if rule.getKind == ``Lean.Parser.Tactic.rwRule then lspPos? fileMap rule else none
  -- `rw` puts the final `rfl` on the "]" token
  let rbracketStart := lspPos? fileMap ruleSeq[2]

  return steps.map fun step =>
    if ruleStarts.any (isSamePosition step.position.start) then
      let rule := (step.tacticString.trimAscii.toString.dropEndWhile (· == ',')).toString
      { step with tacticString := s!"{tacticName} [{rule}]" }
    else if rbracketStart.any (isSamePosition step.position.start) then
      { step with tacticString := "rfl" }
    else
      step

def prettifySteps (fileMap : FileMap) (stx : Syntax) (steps : List ProofStep) (tacticString : String) : List ProofStep := Id.run do
  match stx with
  | `(tactic| intro $_ $_ $_*) =>
    -- intro with 2+ names generates one child TacticInfo per name; merge into a single step
    if steps.isEmpty then return steps
    return [{ steps.head! with
      tacticString        := tacticString,
      goalsAfter          := steps.getLast!.goalsAfter,
      tacticDependsOn     := (steps.flatMap (·.tacticDependsOn)).eraseDups }]
  | _ => return prettifyRwSteps fileMap stx steps

-- Comparator for names, e.g. so that _uniq.34 and _uniq.102 go in the right order.
-- That's not completely right because it doesn't compare prefixes but
-- it's much shorter to write than correct version and serves the purpose.
def nameNumLt (n1 n2 : Name) : Bool :=
  match n1, n2 with
  | .num _ n₁, .num _ n₂ => n₁ < n₂
  | .num _ _,  _ => true
  | _, _ => false

def getProofStepPosition (fileMap : FileMap) (tacticSubstring: Substring.Raw) : ProofStepPosition := {
  start := Lean.FileMap.utf8PosToLspPos fileMap tacticSubstring.startPos,
  stop  := Lean.FileMap.utf8PosToLspPos fileMap tacticSubstring.stopPos
}

/--
  [Claude comment]

  `simpa` runs `simp` and then closes the goal by assigning it directly, so only the
  `simp` half leaves a `TacticInfo` behind. Its step claims the same `goalBefore` as
  `simpa` itself, which suppresses `simpa`'s own (closing) step below - leaving the
  simp-normalized goal looking unsolved. So we drop the expansion and let `simpa`
  stand as one closing step.

  The expansion is recognized by its position: it starts where `simpa` itself starts,
  whereas a nested proof (`simpa using foo (by positivity)`) starts further in and is kept.
-/
def dropSimpaExpansion (position : ProofStepPosition) (steps : List ProofStep) (allGoals : Std.HashSet GoalInfo)
    : List ProofStep × Std.HashSet GoalInfo :=
  let (expansion, kept) := steps.partition (isSamePosition ·.position.start position.start)
  -- The goals the expansion introduced go too, otherwise they resurface as `spawnedGoals`
  (kept, (expansion.flatMap stepGoalsAfter).foldl Std.HashSet.erase allGoals)

def parseTacticBody (fileMap : FileMap) (ctx : ContextInfo) (tInfo : TacticInfo) (tacticSubstring : Substring.Raw) (steps : List ProofStep) (allGoals : Std.HashSet GoalInfo) (tacticString : String) (theorems : List TheoremSignature) : MetaM Result := do
  let position := getProofStepPosition fileMap tacticSubstring
  let (steps, allGoals) := if tInfo.stx.getKind == ``Lean.Parser.Tactic.simpa
    then dropSimpaExpansion position steps allGoals
    else (steps, allGoals)
  let steps := prettifySteps fileMap tInfo.stx steps tacticString

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
    let .some tacticSubstring := getTacticSubstring tInfo | return { steps, allGoals }
    let tacticString := prettifyTacticString (Substring.Raw.toString tacticSubstring)
    parseTacticBody fileMap ctx tInfo tacticSubstring steps allGoals tacticString []
  )

public def BetterParser_SingleTactic (fileMap: FileMap) (infoTree: InfoTree) (ctx : ContextInfo) (info : Info) (steps : List ProofStep) (allGoals : Std.HashSet GoalInfo) (forcedTacticString : String) : MetaM Result := do
  -- 1. Parse tactic
  let .some ctx := info.updateContext? ctx               | panic! "unexpected context node"
  let .ofTacticInfo tInfo := info                        | return { steps, allGoals }
  let .some tacticSubstring := getTacticSubstring tInfo  | return { steps, allGoals }
  let tacticString := if forcedTacticString.length > 0
    then forcedTacticString
    else prettifyTacticString (Substring.Raw.toString tacticSubstring)
  let theorems ← GetTheorems infoTree tInfo ctx
  parseTacticBody fileMap ctx tInfo tacticSubstring steps allGoals tacticString theorems

end PaperproofMcp.Services
-- Services/GoalsAt.lean + ShouldRenderSingleSequent.lean + PrettifyRwTactic.lean +
-- CheckIfUserIsStillTyping.lean — the extra services needed for single-tactic mode.
namespace PaperproofMcp.Services
open Lean Elab Meta Server RequestM

-- DIRECT copy of Lean's `InfoTree.goalsAt?`, plus the `!isClosingBracketInRewriteSequence`
-- adjustment so a cursor on `]` shows the whole rewrite sequence, not a lone `]`.
public partial def goalsAt? (t : InfoTree) (text : FileMap) (hoverPos : String.Pos.Raw) : List GoalsAtResult :=
  let gs := t.collectNodesBottomUp fun ctx i cs gs => Id.run do
    if let Info.ofTacticInfo ti := i then
      if let (some pos, some tailPos) := (i.pos?, i.tailPos?) then
        let trailSize := i.stx.getTrailingSize
        let atEOF := tailPos.byteIdx + trailSize == text.source.rawEndPos.byteIdx
        if pos ≤ hoverPos ∧ (hoverPos.byteIdx < tailPos.byteIdx + max 1 trailSize || atEOF) then
          let isClosingBracketInRewriteSequence := ti.stx.getAtomVal == "]"
          if (gs.isEmpty || (hoverPos ≥ tailPos && gs.all (·.indented))) && !isClosingBracketInRewriteSequence then
            return [{
              ctxInfo := ctx
              tacticInfo := ti
              useAfter := hoverPos > pos && !cs.any (hasNestedTactic pos tailPos)
              indented := (text.toPosition pos).column > (text.toPosition hoverPos).column && !isEmptyBy ti.stx
              priority := if hoverPos.byteIdx == tailPos.byteIdx + trailSize then 0 else 1
            }]
    return gs
  let maxPrio? := gs.map (·.priority) |>.max?
  gs.filter (some ·.priority == maxPrio?)
where
  hasNestedTactic (pos tailPos) : InfoTree → Bool
    | InfoTree.node i@(Info.ofTacticInfo _) cs => Id.run do
      if let `(by $_) := i.stx then
        return false
      if let (some pos', some tailPos') := (i.pos?, i.tailPos?) then
        if tailPos' > hoverPos && (pos', tailPos') != (pos, tailPos) then
          return true
      cs.any (hasNestedTactic pos tailPos)
    | InfoTree.node (Info.ofMacroExpansionInfo _) cs =>
      cs.any (hasNestedTactic pos tailPos)
    | _ => false
  isEmptyBy (stx : Syntax) : Bool :=
    stx.getNumArgs == 2 && stx[0].isToken "by" && stx[1].getNumArgs == 1 && stx[1][0].isMissing

public def shouldRenderSingleSequent (tacticInfo : TacticInfo) (text : FileMap) (hoverPos : String.Pos.Raw) : RequestM Bool := do
  let .some tacticSubstring := tacticInfo.stx.getSubstring? | throwThe RequestError ⟨.invalidParams, "couldntFindTacticSubstring"⟩
  let file : String := Lean.FileMap.source text
  let charBefore := hoverPos.prev file |>.get file
  let charAfter  := hoverPos.get file
  let atEOF      := hoverPos.atEnd file
  let isNotOnTactic := charBefore.isWhitespace && (charAfter.isWhitespace || atEOF)
  let isBy := tacticSubstring.toString.trimAscii.toString == "by"
  return isNotOnTactic || isBy

inductive PpRwState
  | start
  | tacticStringWillOccurSoon
  | tacticStringStarted

def getClosestRw (text: Lean.FileMap) (hoverPos: String.Pos.Raw) : Id String := do
  let mut currentPosition : String.Pos.Raw := hoverPos
  let text : String := Lean.FileMap.source text
  let mut state : PpRwState := PpRwState.start
  let mut rwList : List Char := []
  while currentPosition != 0 do
    currentPosition := currentPosition.prev text
    let currentChar := currentPosition.get text
    match state with
    | PpRwState.start =>
      if currentChar.toString == "[" then
        state := PpRwState.tacticStringWillOccurSoon
    | PpRwState.tacticStringWillOccurSoon =>
      if !currentChar.isWhitespace && !currentChar.isDigit then
        state := PpRwState.tacticStringStarted
        rwList := currentChar :: rwList
    | PpRwState.tacticStringStarted =>
      if !currentChar.isWhitespace then
        rwList := currentChar :: rwList
      else
        break
  return String.ofList rwList

def isTacticRwRule (tacticInfo: TacticInfo) : Bool :=
  let string : String := tacticInfo.stx.formatStx.pretty
  string.startsWith "[(Tactic.rwRule"

public def prettifyRwTactic (tacticInfo : TacticInfo) (text : FileMap) (hoverPos : String.Pos.Raw) : RequestM String := do
  if (isTacticRwRule tacticInfo) then
    let .some tacticSubstring := getTacticSubstring tacticInfo | return ""
    let closestRwTacticName := getClosestRw text hoverPos
    let tacticStr := Substring.Raw.toString tacticSubstring
    let rwRule := ((tacticStr.splitOn ",").head?.getD tacticStr).trimAscii.toString
    pure s!"{closestRwTacticName} [{rwRule}]"
  else
    pure ""

public def checkIfUserIsStillTyping (snap : Snapshots.Snapshot) (hoverPos : Lsp.Position) : RequestM Unit := do
  if let some beginPosition := snap.stx.getPos? then
    let doc ← readDoc
    let text := doc.meta.text
    let snapBegins := text.utf8PosToLspPos beginPosition
    let isSyntaxError := hoverPos.line < snapBegins.line
    if isSyntaxError then
      throwThe RequestError ⟨.invalidParams, "stillTyping"⟩
    for (msg : Message) in MessageLog.toList snap.msgLog do
      let messageHappened := text.leanPosToLspPos msg.pos
      if messageHappened.line >= snapBegins.line then
        let isError := match msg.severity with
          | MessageSeverity.error => true
          | _ => false
        let isSorried := (← msg.data.toString).startsWith "unsolved goals"
        if isError && !isSorried then
          throwThe RequestError ⟨.invalidParams, "stillTyping"⟩

end PaperproofMcp.Services

-- paperproof-mcp runner
structure PPUsedThm where
  name : String
  kind : String
  signature : String
  deriving Lean.ToJson

open Lean Elab Command Meta in
def ppCollectUsedTheorems (trees : List Lean.Elab.InfoTree) (selfName : Name)
    : MetaM (List PPUsedThm) := do
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
      return some { name := nm.toString, kind, signature : PPUsedThm }
    | none => return none)

public structure PPInput where
  pos : Lean.Lsp.Position
  includeTheorems : Bool
  deriving Lean.FromJson, Lean.ToJson

-- The RPC runner: called by position, `withWaitFindSnapAtPos` resolves the
-- position to the enclosing proof's snapshot, then we parse its infoTree. Must
-- be `public` or the module system mangles its name and the RPC can't find it.
open Lean Elab Server RequestM in
@[server_rpc_method]
public def ppMcpGetProof (params : PPInput) : RequestM (RequestTask String) :=
  withWaitFindSnapAtPos params.pos fun snap => do
    let fileMap := (← readDoc).meta.text
    let some parsed ← RequestM.runTermElabM snap
        (liftM <| PaperproofMcp.Services.BetterParser_Tree fileMap snap.infoTree)
      | throwThe RequestError ⟨.invalidParams, "noParsedTree"⟩
    let rawId := snap.stx.find? (·.isOfKind ``Lean.Parser.Command.declId)
      |>.map (·[0].getId) |>.getD Name.anonymous
    let thms ← if params.includeTheorems then
        RequestM.runTermElabM snap (liftM <| ppCollectUsedTheorems [snap.infoTree] rawId)
      else pure []
    let out := Lean.Json.mkObj [
      ("name", Lean.toJson rawId.toString),
      ("steps", Lean.toJson parsed.steps),
      ("theorems", Lean.toJson thms)
    ]
    return out.compress

-- Single-tactic mode: mirrors the library's `getSnapshotData` `.single_tactic`
-- branch — one step for the tactic under the cursor (or a lone sequent when the
-- cursor is between tactics).
open Lean Elab Server RequestM in
@[server_rpc_method]
public def ppMcpGetSingleTactic (params : PPInput) : RequestM (RequestTask String) :=
  withWaitFindSnapAtPos params.pos fun snap => do
    let fileMap := (← readDoc).meta.text
    PaperproofMcp.Services.checkIfUserIsStillTyping snap params.pos
    let hoverPos : String.Pos.Raw := fileMap.lspPosToUtf8Pos params.pos
    let some goalsAtResult := (PaperproofMcp.Services.goalsAt? snap.infoTree fileMap hoverPos).head?
      | throwThe RequestError ⟨.invalidParams, "zeroProofSteps"⟩
    let tacticInfo := goalsAtResult.tacticInfo
    if ← PaperproofMcp.Services.shouldRenderSingleSequent tacticInfo fileMap hoverPos then
      let some mvarId := tacticInfo.goalsAfter.head?
        | throwThe RequestError ⟨.invalidParams, "noGoalsAfter"⟩
      let goal ← liftM <| goalsAtResult.ctxInfo.runMetaM {}
        (PaperproofMcp.Services.printGoalInfo goalsAtResult.ctxInfo mvarId)
      let fakeStep : PaperproofMcp.Services.ProofStep := {
        tacticString    := "fake"
        goalBefore      := goal
        goalsAfter      := [goal]
        tacticDependsOn := []
        spawnedGoals    := []
        position        := { start := ⟨0, 0⟩, stop := ⟨0, 0⟩ }
        theorems        := []
      }
      let out := Lean.Json.mkObj [
        ("name", Lean.toJson ""),
        ("steps", Lean.toJson [fakeStep]),
        ("theorems", Lean.Json.arr #[])
      ]
      return out.compress
    else
      let forcedTacticString : String ← PaperproofMcp.Services.prettifyRwTactic tacticInfo fileMap hoverPos
      let info : Info := Elab.Info.ofTacticInfo tacticInfo
      let parsedTree ← RequestM.runTermElabM snap
        (liftM <| PaperproofMcp.Services.BetterParser_SingleTactic fileMap snap.infoTree goalsAtResult.ctxInfo info [] ∅ forcedTacticString)
      let out := Lean.Json.mkObj [
        ("name", Lean.toJson ""),
        ("steps", Lean.toJson parsedTree.steps),
        ("theorems", Lean.Json.arr #[])
      ]
      return out.compress

