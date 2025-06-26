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
  deriving Inhabited, FromJson, ToJson

@[server_rpc_method]
def getSnapshotData (params : InputParams) : RequestM (RequestTask OutputParams) := do
  withWaitFindSnapAtPos params.pos fun snap => do
    checkIfUserIsStillTyping snap params.pos
    if params.mode == "single_tactic" then
      let hoverPos := ((← readDoc).meta.text).lspPosToUtf8Pos params.pos
      let some tactic := (snap.infoTree.goalsAt? (← readDoc).meta.text hoverPos).head?
        | throwThe RequestError ⟨.invalidParams, "noGoalsAtResult"⟩
      let info := Elab.Info.ofTacticInfo tactic.tacticInfo
      let parsedTree ← parseTacticInfo snap.infoTree tactic.ctxInfo info [] ∅ (ifReturnTheorems := true)
      return { steps := parsedTree.steps, version := 3 }
    else
      let some parsedTree ← BetterParser snap.infoTree
        | throwThe RequestError ⟨.invalidParams, "noParsedTree"⟩
      -- This happens when we hover over something other than a theorem
      if parsedTree.steps.length == 0 then
        throwThe RequestError ⟨.invalidParams, "zeroProofSteps"⟩
      return { steps := parsedTree.steps, version := 3 }
