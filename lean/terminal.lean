/-
  # Terminal Output
  Paperproof supports static extraction of its proof structures to JSON files via terminal execution. 
  This feature is useful for data processing in AI applications.

  To use this feature, first import and build Paperproof. Then in your `lakefile.lean`, write:

    ```lean
    @[default_target]
    lean_exe terminal where
      srcDir := ".lake/packages/Paperproof/lean"
      supportInterpreter := true
    ```

  Now you can run

    ```shell
    lake exe terminal LEAN_FILE_PATH CONSTANT_NAME OUTPUT_PATH
    ```

  in the terminal to save the proof structure of a theorem (lemma, etc.) as a JSON file.

  Here, `CONSTANT_NAME` is the name of your theorem in the lean file. `OUTPUT_PATH` is the path for the output JSON file. 
  For example, run `lake exe terminal ./Examples.lean example_theorem ./output.json`
  to save information in `output.json`.
-/
import Lean
import Services.BetterParser
import Services.GetTheorems

open Lean Elab Paperproof.Services

def dummyPosition : ProofStepPosition := {
  start := { line := 0, character := 0 },
  stop := { line := 0, character := 0 }
}

-- Add ToJson instance for Result (original doesn't have one)
instance : ToJson Result where
  toJson r := Json.mkObj [
    ("steps", toJson r.steps),
    ("allGoals", toJson (r.allGoals.toList))
  ]

-- Static version of printGoalInfo for MetaM (not RequestM)
def static_printGoalInfo (printCtx : ContextInfo) (id : MVarId) : MetaM GoalInfo := do
  let some decl := printCtx.mctx.findDecl? id
    | throwError "Goal not found in mctx"
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
      value    := value.map (fun x => x.fmt.pretty),
      id       := hypDecl.fvarId.name.toString,
      isProof  := isProof
    } : Hypothesis) :: acc)
  return {
    username := decl.userName.toString
    type     := (← ppExprWithInfos ppContext decl.type).fmt.pretty
    hyps     := hyps
    id       := id
  }

-- Static version of getUnassignedGoals for MetaM
def static_getUnassignedGoals (goals : List MVarId) (mctx : MetavarContext) : MetaM (List MVarId) := do
  goals.filterMapM fun id => do
    if let none := mctx.findDecl? id then
      return none
    if mctx.eAssignment.contains id || mctx.dAssignment.contains id then
      return none
    return some id

-- Static version of getGoalsChange for MetaM
def static_getGoalsChange (ctx : ContextInfo) (tInfo : TacticInfo) : MetaM (List (List String × GoalInfo × List GoalInfo)) := do
  let goalMVars := tInfo.goalsBefore ++ tInfo.goalsAfter
  let printCtx := {ctx with mctx := tInfo.mctxAfter}
  let mut goalsBefore ← static_getUnassignedGoals goalMVars tInfo.mctxBefore
  let mut goalsAfter ← static_getUnassignedGoals goalMVars tInfo.mctxAfter
  let commonGoals := goalsBefore.filter fun g => goalsAfter.contains g
  goalsBefore := goalsBefore.filter (!commonGoals.contains ·)
  goalsAfter := goalsAfter.filter (!commonGoals.contains ·)
  
  let mut result : List (List String × GoalInfo × List GoalInfo) := []
  for goalBefore in goalsBefore do
    if let some goalDecl := tInfo.mctxBefore.findDecl? goalBefore then
      let assignedMVars ← ctx.runMetaM goalDecl.lctx (findMVarsAssigned goalBefore tInfo.mctxAfter)
      let tacticDependsOn ← ctx.runMetaM goalDecl.lctx (findHypsUsedByTactic goalBefore goalDecl tInfo.mctxAfter)
      
      result := (
        tacticDependsOn,
        ← static_printGoalInfo printCtx goalBefore,
        ← goalsAfter.filter assignedMVars.contains |>.mapM (static_printGoalInfo printCtx)
      ) :: result
  return result

-- We can eliminate this entirely and just call findTheoremsLikeHover directly!
-- This is exactly what the original GetTheorems does, just with MetaM instead of RequestM

-- Reuse existing prettifySteps, just provide original ProofStep with dummy position
-- No need for separate static version!

-- Static version of parseTacticInfo using original ProofStep structure
partial def static_parseTacticInfo (infoTree: InfoTree) (ctx : ContextInfo) (info : Info) (steps : List ProofStep) (allGoals : Std.HashSet GoalInfo) : MetaM Result := do
  let .some ctx := info.updateContext? ctx | panic! "unexpected context node"
  let .ofTacticInfo tInfo := info          | return { steps, allGoals }
  let .some tacticSubstring := getTacticSubstring tInfo | return { steps, allGoals }

  let tacticString := prettifyTacticString tacticSubstring.toString
  let steps := prettifySteps tInfo.stx steps  -- Use original function!

  let proofTreeEdges ← static_getGoalsChange ctx tInfo
  let currentGoals := proofTreeEdges.map (fun ⟨ _, g₁, gs ⟩ => g₁ :: gs)  |>.flatten
  let allGoals := allGoals.insertMany $ currentGoals
  
  -- Use original stepGoalsAfter and noInEdgeGoals functions!
  let orphanedGoals := currentGoals.foldl Std.HashSet.erase (noInEdgeGoals allGoals steps)
    |>.toArray.insertionSort (nameNumLt ·.id.name ·.id.name) |>.toList

  -- Call findTheoremsLikeHover directly instead of going through wrapper
  let theorems ← 
    match ctx.mctx.findDecl? tInfo.goalsBefore.head!, getTacticSubstring tInfo with
    | some goalDecl, some tacticSubstring =>
      ctx.runMetaM goalDecl.lctx do
        findTheoremsLikeHover infoTree tacticSubstring.startPos tacticSubstring.stopPos ctx goalDecl
    | _, _ => pure []
  let newSteps := proofTreeEdges.filterMap fun ⟨ tacticDependsOn, goalBefore, goalsAfter ⟩ =>
    if steps.map (·.goalBefore) |>.elem goalBefore then
      none
    else
      some {
        tacticString,
        goalBefore,
        goalsAfter,
        tacticDependsOn,
        spawnedGoals := orphanedGoals,
        position := dummyPosition,  -- Just use dummy position!
        theorems := theorems
      }

  return { steps := newSteps ++ steps, allGoals }

partial def static_postNode (infoTree: InfoTree) (ctx : ContextInfo) (info : Info) (results : List (Option Result)) : MetaM Result := do
  let results : List Result := results.filterMap id
  let steps : List ProofStep := (results.map (λ result => result.steps)).flatten
  let allGoals : Std.HashSet GoalInfo := Std.HashSet.ofList ((results.map (λ result => result.allGoals.toList)).flatten)

  static_parseTacticInfo infoTree ctx info steps allGoals

partial def static_BetterParser (infoTree : InfoTree) := infoTree.visitM (postNode :=
  λ ctx info _ results => static_postNode infoTree ctx info results
)










structure Config where
  file_path : System.FilePath := "."
  const_name : Lean.Name := `Unknown
  output_path : System.FilePath := "."


def parseArgs (args : Array String) : IO Config := do
  if args.size < 3 then
    throw <| IO.userError "usage:lean exe terminal FILE_PATH CONST_NAME OUTPUT_FILE_PATH"
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


def writeGoalInfo (goal : Paperproof.Services.GoalInfo) : IO Unit := do
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
    for (goal, i) in step.goalsAfter.zipIdx do
      IO.println s!"Goal {i + 1}:"
      writeGoalInfo goal
  if !step.spawnedGoals.isEmpty then
    IO.println s!"Spawned goals: {step.spawnedGoals.length}"
    for (goal, i) in step.spawnedGoals.zipIdx do
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
        let ioComputation := ((static_BetterParser tree).run {} {}).toIO ctx state
        let ((result, _), _) ← ioComputation
        match result with
        | some r => printresult r config.output_path
        | none => IO.println "Error"
      break
