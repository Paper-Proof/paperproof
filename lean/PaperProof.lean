import Lean
import BetterParser
import CheckIfUserIsStillTyping

open Lean Elab Server RequestM

structure InputParams where
  pos : Lsp.Position
  deriving FromJson, ToJson

structure OutputParams where
  steps : List ProofStep
  deriving Inhabited, FromJson, ToJson

@[server_rpc_method]
def getSnapshotData (params : InputParams) : RequestM (RequestTask OutputParams) := do
  withWaitFindSnapAtPos params.pos fun snap => do
    checkIfUserIsStillTyping snap params.pos

    -- lakesare:
    -- Just thinking about making `TacticApplication`s have `isFocused: true`.
    -- This way hovers will be more under our control & we'll know the "focus path".
    -- We know the focus path just via "who is a parent window of whom" either way though.

    -- (partially copypasted from https://github.com/leanprover/lean4/blob/1f3ef28a1dfe903c0a62663fee4301e6da015942/src/Lean/Server/FileWorker/RequestHandling.lean#L205)
    -- let doc ← readDoc
    -- let text := doc.meta.text
    -- let hoverPos := text.lspPosToUtf8Pos params.pos
    -- let focusedGoals : List GoalsAtResult := snap.infoTree.goalsAt? text hoverPos

    let parsedTree ← parse none snap.infoTree
    -- This happens when we hover over something other than a theorem
    if (parsedTree.steps.length == 0) then
      throwThe RequestError ⟨.invalidParams, "zeroProofSteps"⟩
    return {
      steps := parsedTree.steps
    }
