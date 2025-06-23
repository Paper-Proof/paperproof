import Lean
import BetterParser
import CheckIfUserIsStillTyping

open Lean Server RequestM

structure InputParams where
  pos : Lsp.Position
  -- "single_tactic" or "tree"
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
      let tacticsAtThisPosition : List Elab.GoalsAtResult := snap.infoTree.goalsAt? (← readDoc).meta.text hoverPos
      let some tactic := tacticsAtThisPosition.head? | throwThe RequestError ⟨.invalidParams, "noGoalsAtResult"⟩
      let some ctx := Elab.Info.updateContext? tactic.ctxInfo (Elab.Info.ofTacticInfo tactic.tacticInfo) | throwThe RequestError  ⟨.invalidParams, "couldntUpdateContext"⟩
      let parsedTree ← parseTacticInfo ctx tactic.tacticInfo [] ∅
      return { steps := parsedTree.steps, version := 3 }
    else
      let some parsedTree ← BetterParser snap.infoTree | throwThe RequestError ⟨.invalidParams, "noParsedTree"⟩
      -- This happens when we hover over something other than a theorem
      if (parsedTree.steps.length == 0) then
        throwThe RequestError ⟨.invalidParams, "zeroProofSteps"⟩
      return { steps := parsedTree.steps, version := 3 }
