import Lean

open Lean Elab


def getTacticSubstring (tInfo : TacticInfo) : Option Substring :=
  match tInfo.stx.getSubstring? with
  | .some substring => substring
  | .none => none

structure ArgumentInfo where
  name : String
  type : String
  deriving Inhabited, FromJson, ToJson

structure TheoremSignature where
  name              : String
  instanceArgs      : List ArgumentInfo := [] -- []
  implicitArgs      : List ArgumentInfo := [] -- {}
  explicitArgs      : List ArgumentInfo := [] -- ()
  type              : String := ""            -- return type
  declarationType   : String := ""            -- declaration type
  body              : Option String := none   -- definition body if applicable
  deriving Inhabited, FromJson, ToJson

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
def isInRange (substr : Substring) (startPos stopPos : String.Pos) : Bool :=
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
def findTheoremsLikeHover (tree : Elab.InfoTree) (tacticStartPos tacticStopPos : String.Pos) (ctx : ContextInfo) (goalDecl : MetavarDecl) : MetaM (List TheoremSignature) := do
  let mut theoremNames : NameSet := {}

  -- Sample positions throughout the tactic range (every few characters)
  -- This ensures we catch all identifiers that would show on hover
  let mut currentPos := tacticStartPos
  let step : String.Pos := ⟨3⟩  -- Check every 3 characters

  while currentPos < tacticStopPos do
    -- Use Lean's actual hover function to find what would show at this position
    if let some infoWithCtx := tree.hoverableInfoAt? currentPos then
      -- Extract theorem name from the hover info
      match infoWithCtx.info with
      | .ofTermInfo termInfo =>
        if let some name := extractTheoremName termInfo.expr termInfo.lctx then
          theoremNames := theoremNames.insert name
      | _ => pure ()

    currentPos := currentPos + step

  -- Process each theorem name and filter for relevant declarations
  let theoremSignatures ← theoremNames.toList.filterMapM fun name => do
    let resolvedName ← resolveGlobalConstNoOverloadCore name
    processDeclaration resolvedName ctx goalDecl

  pure theoremSignatures


def GetTheoremsq (infoTree : InfoTree) (tacticInfo : TacticInfo) (ctx : ContextInfo) : MetaM (List TheoremSignature) := do
  let some goalDecl := ctx.mctx.findDecl? tacticInfo.goalsBefore.head!
    | throwError "error"
  let some tacticSubstring := getTacticSubstring tacticInfo
    | throwError "error"

  ctx.runMetaM goalDecl.lctx do
    findTheoremsLikeHover infoTree tacticSubstring.startPos tacticSubstring.stopPos ctx goalDecl








structure Hypothesis where
  username : String
  type : String
  value : Option String
  -- unique identifier for the hypothesis, fvarId
  id : String
  isProof : String
  deriving Inhabited, ToJson, FromJson

structure GoalInfo where
  username : String
  type : String
  hyps : List Hypothesis
  -- unique identifier for the goal, mvarId
  id : MVarId
  deriving Inhabited, ToJson, FromJson

instance : BEq GoalInfo where
  beq g1 g2 := g1.id == g2.id

instance : Hashable GoalInfo where
  hash g := hash g.id

-- structure ProofStepPosition where
--   start: Lsp.Position
--   stop: Lsp.Position
--   deriving Inhabited, ToJson, FromJson

structure ProofStep where
  tacticString    : String
  goalBefore      : GoalInfo
  goalsAfter      : List GoalInfo
  tacticDependsOn : List String
  spawnedGoals    : List GoalInfo
  --position        : ProofStepPosition
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

def printGoalInfo (printCtx : ContextInfo) (id : MVarId) : MetaM GoalInfo := do
  let some decl := printCtx.mctx.findDecl? id
    | throwError "error"
  -- to get tombstones in name ✝ for unreachable hypothesis
  let lctx := decl.lctx |>.sanitizeNames.run' {options := {}}
  let ppContext := printCtx.toPPContext lctx
  let hyps ← lctx.foldrM (init := []) (fun hypDecl acc => do
    if hypDecl.isAuxDecl || hypDecl.isImplementationDetail then
      return acc
    let type ← liftM (ppExprWithInfos ppContext hypDecl.type)
    let value ← liftM (hypDecl.value?.mapM (ppExprWithInfos ppContext))
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

def getUnassignedGoals (goals : List MVarId) (mctx : MetavarContext) : MetaM (List MVarId) := do
  goals.filterMapM fun id => do
    if let none := mctx.findDecl? id then
      return none
    if mctx.eAssignment.contains id ||
       mctx.dAssignment.contains id then
      return none
    return some id

structure Result where
  steps : List ProofStep
  allGoals : Std.HashSet GoalInfo

instance : ToJson Result where
  toJson r := Json.mkObj [
    ("steps", toJson r.steps),
    ("allGoals", toJson (r.allGoals.toList))
  ]

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

def prettifySteps (stx : Syntax) (steps : List ProofStep) : List ProofStep := Id.run do
  match stx with
  | `(tactic| rw [$_,*] $(_)?)
  | `(tactic| rewrite [$_,*] $(_)?) =>
    let prettify (tStr : String) :=
      let res := tStr.trim.dropRightWhile (· == ',')
      -- rw puts final rfl on the "]" token
      if res == "]" then "rfl" else res
    return steps.map fun a => { a with tacticString := s!"rw [{prettify a.tacticString}]" }
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
  (tacticString.splitOn "\n").head!.trim


partial def parseTacticInfo (infoTree: InfoTree) (ctx : ContextInfo) (info : Info) (steps : List ProofStep) (allGoals : Std.HashSet GoalInfo) (isSingleTacticMode : Bool) (forcedTacticString : String := "") : MetaM Result := do
  let .some ctx := info.updateContext? ctx | panic! "unexpected context node"
  let .ofTacticInfo tInfo := info          | return { steps, allGoals }
  let .some tacticSubstring := getTacticSubstring tInfo | return { steps, allGoals }

  let mut tacticString := if forcedTacticString.length > 0 then forcedTacticString else prettifyTacticString tacticSubstring.toString

  let steps := prettifySteps tInfo.stx steps

  --let position ← sorry

  let proofTreeEdges ← getGoalsChange ctx tInfo
  let currentGoals := proofTreeEdges.map (fun ⟨ _, g₁, gs ⟩ => g₁ :: gs)  |>.flatten
  let allGoals := allGoals.insertMany $ currentGoals
  -- It's like tacticDependsOn but unnamed mvars instead of hyps.
  -- Important to sort for have := calc for example, e.g. calc 3 < 4 ... 4 < 5 ...
  let orphanedGoals := currentGoals.foldl Std.HashSet.erase (noInEdgeGoals allGoals steps)
    |>.toArray.insertionSort (nameNumLt ·.id.name ·.id.name) |>.toList

  let theorems ←  GetTheoremsq infoTree tInfo ctx  -- FOR STATIC VERSION, WE DELETE "IF SINGLETACTIC MODE"
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
        --position := position
        theorems := theorems
      }

  return { steps := newSteps ++ steps, allGoals }


partial def postNode (infoTree: InfoTree) (ctx : ContextInfo) (info : Info) (results : List (Option Result)) : MetaM Result := do
  -- Remove `Option.none` values from the `results` list (we have them because of the `.visitM` implementation)
  let results : List Result := results.filterMap id
  -- 1. Flatten `ProofStep`s
  let steps : List ProofStep := (results.map (λ result => result.steps)).flatten
  -- 2. Flatten `GoalInfo`s
  let allGoals : Std.HashSet GoalInfo := Std.HashSet.ofList ((results.map (λ result => result.allGoals.toList)).flatten)

  parseTacticInfo infoTree ctx info steps allGoals (isSingleTacticMode := false)


partial def BetterParser (infoTree : InfoTree) := infoTree.visitM (postNode :=
  λ ctx info _ results => postNode infoTree ctx info results
)










structure Config where
  file_path : System.FilePath := "."
  const_name : Lean.Name := `Unknown
  output_path : System.FilePath := "."


def parseArgs (args : Array String) : IO Config := do
  if args.size < 3 then
    throw <| IO.userError "usage:lean exe goaltree FILE_PATH CONST_NAME OUTPUT_FILE_PATH"
  let mut cfg : Config := {}
  cfg := { cfg with file_path := ⟨args[0]!⟩ }
  cfg := { cfg with const_name := args[1]!.toName }
  cfg := { cfg with output_path := ⟨args[2]!⟩ }
  IO.println (s!"File:{cfg.file_path}")
  IO.println (s!"Constant:{cfg.const_name}")
  IO.println (s!"Output:{cfg.output_path}")

  return cfg


unsafe def processCommands : Frontend.FrontendM (List (Lean.Environment × InfoState)) := do
  let done ← Lean.Elab.Frontend.processCommand
  let st := ← get
  let infoState := st.commandState.infoState
  let env' := st.commandState.env

  -- clear the infostate
  set {st with commandState := {st.commandState with infoState := {}}}
  if done
  then return [(env', infoState)]
  else
    return (env', infoState) :: (←processCommands)




------------------------------------------------------------------
--Codes for printing and saving to Json, use printresult (r:Result) : IO Unit


def writeGoalInfo (goal : GoalInfo) : IO Unit := do
  IO.println s!"Goal: {goal.type}"
  if goal.hyps.isEmpty then
    IO.println "\nNo hypotheses"
  else
    IO.println "\nHypotheses:"
    for hyp in goal.hyps do
      IO.println s!"{hyp.username}:{hyp.type}"
  IO.println "---"

def writeProofStep (step : ProofStep) (stepNumber : Nat) : IO Unit := do
  IO.println s!"\n=== Step {stepNumber} ==="
  IO.println s!"Tactic: {step.tacticString}"
  IO.println s!"\nGoals Before:{step.goalBefore.type}"
  if step.goalsAfter.isEmpty then
    IO.println "\nGoals After: No goals (proof completed)"
  else
    IO.println s!"\nGoals After: {step.goalsAfter.length} goal(s)"
    for (i, goal) in step.goalsAfter.enum do
      IO.println s!"Goal {i + 1}:"
      writeGoalInfo goal
  if !step.spawnedGoals.isEmpty then
    IO.println s!"Spawned goals: {step.spawnedGoals.length}"
    for (i, goal) in step.spawnedGoals.enum do
      IO.println s!"Spawned goal {i + 1}:"
      writeGoalInfo goal

def saveResultToFile (r : Result) (filePath : System.FilePath) : IO Unit := do
  let json := toJson r
  let jsonStr := Json.pretty json
  IO.FS.writeFile filePath jsonStr

def printresult (r : Result)(filePath : System.FilePath) : IO Unit := do
  IO.println "Proof Tree:"
  IO.println "==========="

  if r.steps.isEmpty then
    IO.println "No proof steps"
    return

  let mut stepNumber := 1
  for step in r.steps do
    writeProofStep step stepNumber
    stepNumber := stepNumber + 1

  IO.println "\n=== Summary ==="
  IO.println s!"Total steps: {r.steps.length}"
  IO.println s!"Total goals in proof state: {r.allGoals.size}"

  if !r.allGoals.isEmpty then
    IO.println "\nAll unique goals encountered:"
    for goal in r.allGoals.toList do
      IO.println s!"- {goal.username} : {goal.type}"

  saveResultToFile r filePath











unsafe def main (args : List String) : IO Unit := do
  IO.println ("running..")
  let config ← parseArgs args.toArray
  Lean.searchPathRef.set compile_time_search_path%
  let mut input ← IO.FS.readFile config.file_path
  Lean.enableInitializersExecution
  let inputCtx := Lean.Parser.mkInputContext input config.file_path.toString
  let (header, parserState, messages) ← Lean.Parser.parseHeader inputCtx
  let (env, messages) ← Lean.Elab.processHeader header {} messages inputCtx

  if messages.hasErrors then
    for msg in messages.toList do
      if msg.severity == .error then
        println! "ERROR: {← msg.toString}"
    throw <| IO.userError "Errors during import; aborting"

  let env := env.setMainModule (← Lean.moduleNameOfFileName config.file_path none)

  if env.contains config.const_name then
    throw <| IO.userError s!"constant of name {config.const_name} is already in environment"

  let commandState := { Lean.Elab.Command.mkState env messages {} with infoState.enabled := true }

  let (steps, _frontendState) ← (processCommands.run { inputCtx := inputCtx }).run
    { commandState := commandState, parserState := parserState, cmdPos := parserState.pos }

  -----
  for ⟨env, s⟩ in steps do
    if env.contains config.const_name then
      for tree in s.trees do
        let ctx : Lean.Core.Context := { fileName := "", fileMap := default, options := {} }
        let state : Lean.Core.State := { env := env, messages := Lean.MessageLog.empty }
        let ioComputation := ((BetterParser tree).run {} {}).toIO ctx state
        let ((result, _), _) ← ioComputation
        match result with
        | some r => printresult r config.output_path
        | none => IO.println "Error"
      break
