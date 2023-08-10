import Lean
import Lean.Elab.InfoTree
import Lean.Data.Options
import Lean.Widget
import BetterParser

open Lean Elab
open Lean Meta
open Lean.Elab.Tactic
open Lean Widget
open Server RequestM

structure GetPpContextParams where
  pos : Lsp.Position
  deriving FromJson, ToJson

-- TODO we should move this to another file, read on this (https://leanprover.github.io/functional_programming_in_lean/hello-world/starting-a-project.html)
def checkIfUserIsStillTyping (snap : Snapshots.Snapshot) (hoverPos : Lsp.Position) : RequestM Unit := do
  let doc ← readDoc
  let text := doc.meta.text

  -- If we have this, then it's some syntax error:
  --   snap.beginPos: (101, 0)
  --   snap.endPos: (103, 0)
  --   hoverPos: (93, 4)
  --   => no error messages
  let isSyntaxError := hoverPos.line < (text.utf8PosToLspPos snap.beginPos).line

  let mut isThereSeriousError := false
  let snapBegins : Lsp.Position := text.utf8PosToLspPos snap.beginPos
  for (msg : Message) in snap.msgLog.msgs do
    -- only log the message if it appeared AFTER the snap.beginPos
    let messageHappened := text.leanPosToLspPos msg.pos
    if messageHappened.line >= snapBegins.line then
      -- Happens in these cases:
      -- .data equals "unknown tactic"
      -- .data equals "expected '(' or term"
      -- .data equals "unknown identifier 'm'"
      -- .data equals "tactic 'apply' failed, failed to unify..."
      let isError := match msg.severity with
        | MessageSeverity.error => true
        | _ => false
      -- Everything's fine, we'll get a nice InfoTree
      let isSorried := (← msg.data.toString).startsWith "unsolved goals"

      isThereSeriousError := isError && !isSorried

    if (isSyntaxError || isThereSeriousError) then
      throwThe RequestError ⟨.invalidParams, "stillTyping"⟩


@[server_rpc_method]
def getPpContext (params : GetPpContextParams) : RequestM (RequestTask Proof) := do
  withWaitFindSnapAtPos params.pos fun snap => do
    checkIfUserIsStillTyping snap params.pos

    -- @anton this is probably slightly cryptic, don't read
    -- lakesare:
    -- Just thinking about making `TacticApplication`s have `isFocused: true`.
    -- This way hovers will be more under our control & we'll know the "focus path".
    -- We know the focus path just via "who is a parent window of whom" either way though.

    -- (partially copypasted from https://github.com/leanprover/lean4/blob/1f3ef28a1dfe903c0a62663fee4301e6da015942/src/Lean/Server/FileWorker/RequestHandling.lean#L205)
    -- let doc ← readDoc
    -- let text := doc.meta.text
    -- let hoverPos := text.lspPosToUtf8Pos params.pos
    -- let focusedGoals : List GoalsAtResult := snap.infoTree.goalsAt? text hoverPos

    let tree := snap.infoTree
    let th ← parse tree
    return th
