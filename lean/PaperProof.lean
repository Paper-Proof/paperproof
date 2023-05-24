import Lean
import Lean.Elab.InfoTree
import Lean.Data.Options
import Lean.Widget
import BetterParser
import FindEdges

open Lean Elab
open Lean Meta
open Lean.Elab.Tactic
open Lean Widget

structure GetPpContextParams where
  pos : Lsp.Position
  deriving FromJson, ToJson

open Server RequestM in
@[server_rpc_method]
def getPpContext (params : GetPpContextParams) : RequestM (RequestTask String) := do
  withWaitFindSnapAtPos params.pos fun snap => do
    let tree := snap.infoTree
    let tactics ← parse tree
    return s!"{tactics.map toJson}"
    -- return s!"{(findEdges tactics).map toJson}"