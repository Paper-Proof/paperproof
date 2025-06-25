import Lean
import Lean.Meta.Basic
import Lean.Elab.Tactic

import BetterParser
import CheckIfUserIsStillTyping
import GetTheoremsUsedInTactic

open Lean Elab Meta Server RequestM

structure InputParams where
  pos : Lsp.Position
  mode: String
  deriving FromJson, ToJson

structure OutputParams where
  steps  : List ProofStep
  version: Nat
  theorems : List TheoremSignature := []
  deriving Inhabited, FromJson, ToJson

@[server_rpc_method]
def getSnapshotData (params : InputParams) : RequestM (RequestTask OutputParams) := do
  withWaitFindSnapAtPos params.pos fun snap => do
    checkIfUserIsStillTyping snap params.pos
    if params.mode == "single_tactic" then
      let hoverPos := ((← readDoc).meta.text).lspPosToUtf8Pos params.pos
      let some tactic := (snap.infoTree.goalsAt? (← readDoc).meta.text hoverPos).head?
        | throwThe RequestError ⟨.invalidParams, "noGoalsAtResult"⟩
      let some ctx := Elab.Info.updateContext? tactic.ctxInfo (Elab.Info.ofTacticInfo tactic.tacticInfo)
        | throwThe RequestError ⟨.invalidParams, "couldntUpdateContext"⟩
      
      let parsedTree ← parseTacticInfo ctx tactic.tacticInfo [] ∅
      let theorems ← GetTheoremsUsedInTactic snap.infoTree tactic.tacticInfo ctx

      return { steps := parsedTree.steps, version := 3, theorems }
    else
      let some parsedTree ← BetterParser snap.infoTree
        | throwThe RequestError ⟨.invalidParams, "noParsedTree"⟩
      if parsedTree.steps.length == 0 then
        throwThe RequestError ⟨.invalidParams, "zeroProofSteps"⟩
      return { steps := parsedTree.steps, version := 3 }
