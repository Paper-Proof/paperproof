module

public import Lean
public import Lean.Meta.Basic
public import Lean.Elab.Tactic

public meta import Services.BetterParser
public meta import Services.CheckIfUserIsStillTyping
public meta import Services.GoalsAt
public meta import Services.PrettifyRwTactic
public meta import Services.ShouldRenderSingleSequent

open Lean Elab Meta Server RequestM

namespace Paperproof

public meta inductive Mode where
  | single_tactic
  | tree
  deriving FromJson, ToJson

public meta structure InputParams where
  pos : Lsp.Position
  mode: Mode
  deriving FromJson, ToJson

public meta structure OutputParams where
  steps : List Paperproof.Services.ProofStep
  deriving Inhabited, FromJson, ToJson

meta def proofSteps (snap : Snapshots.Snapshot) : RequestM (Option (List Paperproof.Services.ProofStep)) := do
  let fileMap := (← readDoc).meta.text
  let some parsedTree ← RequestM.runTermElabM snap (liftM <| Paperproof.Services.BetterParser_Tree fileMap snap.infoTree)
    | return none
  return parsedTree.steps

/-- Accepts a snapshot, and returns the proof in the format that `<Paperproof proof={proof}/>` expects (see https://www.npmjs.com/package/paperproof). -/
public meta def getProof (snapshot : Snapshots.Snapshot) : RequestM (Option Json) := do
  let some steps ← proofSteps snapshot | return none
  if steps.isEmpty then return none
  return toJson steps

@[server_rpc_method]
public meta def getSnapshotData (params : InputParams) : RequestM (RequestTask OutputParams) := do
  withWaitFindSnapAtPos params.pos fun snap => do
    let fileMap : FileMap := (← readDoc).meta.text
    Paperproof.Services.checkIfUserIsStillTyping snap params.pos
    match params.mode with
    | .single_tactic =>
      let hoverPos : String.Pos.Raw := fileMap.lspPosToUtf8Pos params.pos
      let some goalsAtResult := (Paperproof.Services.goalsAt? snap.infoTree fileMap hoverPos).head? | throwThe RequestError ⟨.invalidParams, "zeroProofSteps"⟩
      let tacticInfo := goalsAtResult.tacticInfo

      if ← Paperproof.Services.shouldRenderSingleSequent tacticInfo fileMap hoverPos then
        let some mvarId := tacticInfo.goalsAfter.head?
          | throwThe RequestError ⟨.invalidParams, "noGoalsAfter"⟩
        let goal ← liftM <| goalsAtResult.ctxInfo.runMetaM {} (Paperproof.Services.printGoalInfo goalsAtResult.ctxInfo mvarId)
        let fakeStep : Paperproof.Services.ProofStep := {
          tacticString    := "fake"
          goalBefore      := goal
          goalsAfter      := [goal]
          tacticDependsOn := []
          spawnedGoals    := []
          position        := { start := ⟨0, 0⟩, stop := ⟨0, 0⟩ }
          theorems        := []
        }
        return { steps := [fakeStep] }
      else
        let forcedTacticString : String ← Paperproof.Services.prettifyRwTactic tacticInfo fileMap hoverPos
        let info : Info := Elab.Info.ofTacticInfo tacticInfo
        let parsedTree ← RequestM.runTermElabM snap (liftM <| Paperproof.Services.BetterParser_SingleTactic fileMap snap.infoTree goalsAtResult.ctxInfo info [] ∅ forcedTacticString)
        return { steps := parsedTree.steps }
    | .tree =>
      let some steps ← proofSteps snap
        | throwThe RequestError ⟨.invalidParams, "noParsedTree"⟩
      -- This happens when we hover over something other than a theorem
      if steps.length == 0 then
        throwThe RequestError ⟨.invalidParams, "zeroProofSteps"⟩
      return { steps }

end Paperproof
