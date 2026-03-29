/-
  # Terminal Output
  Paperproof supports static extraction of proof structures to JSON files via terminal.
  This is useful for data processing in AI applications.

  To use this feature, add to your `lakefile.lean`:

    ```lean
    lean_exe terminal where
      srcDir := ".lake/packages/Paperproof/lean"
      supportInterpreter := true
    ```

  Then run:

    ```shell
    lake exe terminal LEAN_FILE_PATH CONSTANT_NAME OUTPUT_PATH
    ```

  For example:

    ```shell
    lake exe terminal ./Examples.lean my_theorem ./output.json
    ```
-/
import Lean
import Services.BetterParser

open Lean Elab Paperproof.Services

instance : ToJson Result where
  toJson r := Json.mkObj [
    ("steps",    toJson r.steps),
    ("allGoals", toJson r.allGoals.toList)
  ]

structure Config where
  filePath   : System.FilePath := "."
  constName  : Lean.Name      := `Unknown
  outputPath : System.FilePath := "."

def parseArgs (args : Array String) : IO Config := do
  if args.size < 3 then
    throw <| IO.userError "usage: lake exe terminal FILE_PATH CONST_NAME OUTPUT_PATH"
  let cfg : Config := {
    filePath   := ⟨args[0]!⟩,
    constName  := args[1]!.toName,
    outputPath := ⟨args[2]!⟩
  }
  IO.println s!"File:     {cfg.filePath}"
  IO.println s!"Constant: {cfg.constName}"
  IO.println s!"Output:   {cfg.outputPath}"
  return cfg

unsafe def processCommands : Frontend.FrontendM (List (Lean.Environment × InfoState)) := do
  let done ← Lean.Elab.Frontend.processCommand
  let st ← get
  let pair := (st.commandState.env, st.commandState.infoState)
  set { st with commandState := { st.commandState with infoState := {} } }
  if done then
    return [pair]
  else
    return pair :: (← processCommands)

def writeGoalInfo (goal : GoalInfo) : IO Unit := do
  IO.println s!"  type: {goal.type}"
  if goal.hyps.isEmpty then
    IO.println s!"  hyps: (none)"
  else
    IO.println s!"  hyps:"
    for hyp in goal.hyps do
      IO.println s!"    {hyp.username} : {hyp.type}"

def writeProofStep (step : ProofStep) (i : Nat) : IO Unit := do
  IO.println s!"[step {i}]"
  IO.println s!"tactic: {step.tacticString}"
  IO.println s!"goalBefore:"
  writeGoalInfo step.goalBefore
  if step.goalsAfter.isEmpty then
    IO.println s!"goalsAfter: (none)"
  else
    IO.println s!"goalsAfter:"
    for goal in step.goalsAfter do writeGoalInfo goal
  if step.spawnedGoals.isEmpty then
    IO.println s!"spawnedGoals: (none)"
  else
    IO.println s!"spawnedGoals:"
    for goal in step.spawnedGoals do writeGoalInfo goal

def printResult (r : Result) (outputPath : System.FilePath) : IO Unit := do
  if r.steps.isEmpty then
    IO.println "No proof steps found."
    return
  for (step, i) in r.steps.zipIdx do
    writeProofStep step (i + 1)
    IO.println ""
  IO.FS.writeFile outputPath (Json.pretty (toJson r))
  IO.println s!"Saved to {outputPath}"

unsafe def main (args : List String) : IO Unit := do
  let config ← parseArgs args.toArray
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let input ← IO.FS.readFile config.filePath
  let inputCtx := Lean.Parser.mkInputContext input config.filePath.toString
  let (header, parserState, messages) ← Lean.Parser.parseHeader inputCtx
  let (env, messages) ← Lean.Elab.processHeader header {} messages inputCtx

  if messages.hasErrors then
    for msg in messages.toList do
      if msg.severity == .error then
        println! "ERROR: {← msg.toString}"
    throw <| IO.userError "Errors during import; aborting"

  let env := env.setMainModule (← Lean.moduleNameOfFileName config.filePath none)

  if env.contains config.constName then
    throw <| IO.userError s!"'{config.constName}' is already in the environment before processing"

  let commandState := { Lean.Elab.Command.mkState env messages {} with infoState.enabled := true }
  let (steps, _) ← (processCommands.run { inputCtx }).run
    { commandState, parserState, cmdPos := parserState.pos }

  let fileMap := Lean.FileMap.ofString input
  for (env, s) in steps do
    if env.contains config.constName then
      for tree in s.trees do
        let ctx   : Core.Context := { fileName := config.filePath.toString, fileMap, options := {} }
        let state : Core.State   := { env }
        let ((result, _), _) ← ((BetterParser_Tree fileMap tree).run {} {}).toIO ctx state
        match result with
        | some r => printResult r config.outputPath
        | none   => IO.println "No proof tree found."
      break
