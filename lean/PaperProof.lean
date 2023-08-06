import Lean
import Lean.Elab.InfoTree
import Lean.Data.Options
import Lean.Widget
import BetterParser

open Lean Elab
open Lean Meta
open Lean.Elab.Tactic
open Lean Widget

structure GetPpContextParams where
  pos : Lsp.Position
  deriving FromJson, ToJson

open Server RequestM in
@[server_rpc_method]
def getPpContext (params : GetPpContextParams) : RequestM (RequestTask Proof) := do
  withWaitFindSnapAtPos params.pos fun snap => do
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
