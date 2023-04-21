import Lean
import Lean.Environment
import Lean.Elab.Frontend
import Lean.Elab.InfoTree
import Lean.Data.Options
import Lean.Widget
import Mathlib.Tactic.Linarith
import Parser

open Lean
open Lean Elab
open Lean Meta
open Lean.Elab.Tactic
open Lean Widget

inductive ProofTree where
  | empty : ProofTree 
  | leaf : (name: String) → (type: String) →  ProofTree
  | node : Frame → Option String → List ProofTree → ProofTree
  deriving Inhabited

partial def ProofTree.toJson : ProofTree → Json 
  | ProofTree.empty => Json.mkObj []
  | ProofTree.leaf f type => Json.mkObj $ [("name", Json.str f), ("type", Json.str type)]
  | ProofTree.node f name ts =>
    let name := name.getD ""
    let ts := ts.map ProofTree.toJson
    Json.mkObj $ [("name", Json.str name), ("children", Json.arr ts.toArray)] ++ (frameJson f)
  where
    frameJson (f : Frame) :=
      [("fromType", Json.str f.fromType), ("toType", Json.str f.toType), ("action", Json.str f.action)]

partial def findTree (name : String) (state : TreeState): ProofTree :=
  if name == solvedEmoji then
    .leaf name ""
  else
    let type := state.types.findD name name
    if let some frame := state.frames.find? (fun f => f.fromType == type) then
      let subTrees := frame.subFrames.map (fun f => findTree f state)
      .node frame
        (if type != name then name else none)
        ((findTree frame.toType state) :: subTrees)
    else if let some d := state.defns.find? (fun f => f.name == name) then
      .leaf s!"{d.name} := {d.defn}" ""
    else 
      .leaf name (state.types.findD name "$$$$")

structure GetPpContextParams where
  pos : Lsp.Position
  deriving FromJson, ToJson

def getTopLevelType (state : TreeState) : Option String := Id.run do
    -- Top level type is the one which is never in the `toType` of `state.frames` and has no entry with name in `state.types`
    let allTypesTo := state.frames.map (fun f => f.toType)
    let allTypesFrom := state.frames.map (fun f => f.fromType)
    let mut haveTypes := []
    for (_, type) in state.types.toList do
      haveTypes := type :: haveTypes 
    let types := allTypesFrom.filter (fun t => !allTypesTo.contains t && !haveTypes.contains t)
    types.head?
 
open Server RequestM in
@[server_rpc_method]
def getPpContext (params : GetPpContextParams) : RequestM (RequestTask String) := do
  withWaitFindSnapAtPos params.pos fun snap => do
    let tree := snap.infoTree
    let (_, state ) ← (parseTacticProof tree).run default
    if let some type := getTopLevelType state then
      let state := {state with types := state.types.insert "top level" type}
      let fragments := findTree "top level" state
      return s!"{fragments.toJson}"
    else
      return "No top level type"

@[widget]
def ppWidget: UserWidgetDefinition := {
  name := "Paper proof"
  javascript:= include_str "widget" / "dist" / "indexExtension.js"
}

structure PaperProofProps where
  kind : String
  deriving ToJson, FromJson, Inhabited

def forBrowser := (toJson { kind := "browser" : PaperProofProps})
#widget ppWidget forBrowser

-- #widget ppWidget (toJson { kind := "extension" : PaperProofProps})

theorem th : ∀ (N : ℕ), ∃ M, N + N = M := by {
  intro n
  exact ⟨ n + n, rfl ⟩
}
