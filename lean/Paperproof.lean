import Lean
import Lean.Meta.Basic
import Lean.Elab.Tactic

import Services.BetterParser
import Services.CheckIfUserIsStillTyping
import Services.GoalsAt
import Services.PrettifyRwTactic

open Lean Elab Meta Server RequestM

namespace Paperproof

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
    Paperproof.Services.checkIfUserIsStillTyping snap params.pos
    match params.mode with
    | .single_tactic =>
      let text : FileMap := (← readDoc).meta.text
      let hoverPos : String.Pos := text.lspPosToUtf8Pos params.pos
      let some tactic := (Paperproof.Services.goalsAt? snap.infoTree text hoverPos).head?
        | throwThe RequestError ⟨.invalidParams, "noGoalsAtResult"⟩
      let info := Elab.Info.ofTacticInfo tactic.tacticInfo
      let forcedTacticString : String ← Paperproof.Services.prettifyRwTactic tactic.tacticInfo text hoverPos
      let parsedTree ← Paperproof.Services.parseTacticInfo snap.infoTree tactic.ctxInfo info [] ∅ (isSingleTacticMode := true) (forcedTacticString := forcedTacticString)
      return { steps := parsedTree.steps, version := 4 }
    | .tree =>
      let some parsedTree ← Paperproof.Services.BetterParser snap.infoTree
        | throwThe RequestError ⟨.invalidParams, "noParsedTree"⟩
      -- This happens when we hover over something other than a theorem
      if parsedTree.steps.length == 0 then
        throwThe RequestError ⟨.invalidParams, "zeroProofSteps"⟩
      return { steps := parsedTree.steps, version := 4 }

end Paperproof
