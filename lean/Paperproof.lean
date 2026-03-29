import Lean
import Lean.Meta.Basic
import Lean.Elab.Tactic

import Services.BetterParser
import Services.CheckIfUserIsStillTyping
import Services.GoalsAt
import Services.PrettifyRwTactic
import Services.ShouldRenderSingleSequent

open Lean Elab Meta Server RequestM

namespace Paperproof

def VERSION := 4

inductive Mode where
  | single_tactic
  | tree
  deriving FromJson, ToJson

structure InputParams where
  pos : Lsp.Position
  mode: Mode
  deriving FromJson, ToJson

structure OutputParams where
  steps  : List Paperproof.Services.ProofStep
  version: Nat
  deriving Inhabited, FromJson, ToJson

@[server_rpc_method]
def getSnapshotData (params : InputParams) : RequestM (RequestTask OutputParams) := do
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
        return { steps := [fakeStep], version := VERSION }
      else
        let forcedTacticString : String ← Paperproof.Services.prettifyRwTactic tacticInfo fileMap hoverPos
        let info : Info := Elab.Info.ofTacticInfo tacticInfo
        let parsedTree ← RequestM.runTermElabM snap (liftM <| Paperproof.Services.BetterParser_SingleTactic fileMap snap.infoTree goalsAtResult.ctxInfo info [] ∅ forcedTacticString)
        return { steps := parsedTree.steps, version := VERSION }
    | .tree =>
      let fileMap := (← readDoc).meta.text
      let some parsedTree ← RequestM.runTermElabM snap (liftM <| Paperproof.Services.BetterParser_Tree fileMap snap.infoTree)
        | throwThe RequestError ⟨.invalidParams, "noParsedTree"⟩
      -- This happens when we hover over something other than a theorem
      if parsedTree.steps.length == 0 then
        throwThe RequestError ⟨.invalidParams, "zeroProofSteps"⟩
      return { steps := parsedTree.steps, version := VERSION }

end Paperproof
