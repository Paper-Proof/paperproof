import Lean
import Lean.Meta.Basic
import Lean.Elab.Tactic

import BetterParser
import CheckIfUserIsStillTyping
import GoalsAt
import GetClosestRw

open Lean Elab Meta Server RequestM

inductive Mode where
  | single_tactic
  | tree
  deriving FromJson, ToJson

structure InputParams where
  pos : Lsp.Position
  mode: Mode
  deriving FromJson, ToJson

structure OutputParams where
  steps  : List ProofStep
  version: Nat
  deriving Inhabited, FromJson, ToJson

@[server_rpc_method]
def getSnapshotData (params : InputParams) : RequestM (RequestTask OutputParams) := do
  withWaitFindSnapAtPos params.pos fun snap => do
    checkIfUserIsStillTyping snap params.pos
    match params.mode with
    | .single_tactic =>
      let text := (← readDoc).meta.text
      let hoverPos : String.Pos := text.lspPosToUtf8Pos params.pos
      let some tactic := (goalsAt? snap.infoTree text hoverPos).head?
        | throwThe RequestError ⟨.invalidParams, "noGoalsAtResult"⟩
      let info := Elab.Info.ofTacticInfo tactic.tacticInfo
      let parsedTree ← parseTacticInfo snap.infoTree tactic.ctxInfo info [] ∅ (isSingleTacticMode := true)
      let closestRwString := getClosestRw text hoverPos
      dbg_trace closestRwString
      return { steps := parsedTree.steps, version := 3 }
    | .tree =>
      let some parsedTree ← BetterParser snap.infoTree
        | throwThe RequestError ⟨.invalidParams, "noParsedTree"⟩
      -- This happens when we hover over something other than a theorem
      if parsedTree.steps.length == 0 then
        throwThe RequestError ⟨.invalidParams, "zeroProofSteps"⟩
      return { steps := parsedTree.steps, version := 3 }
