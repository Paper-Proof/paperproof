import Lean
import Lean.Environment
import Lean.Elab.Frontend
import Lean.Elab.InfoTree
import Lean.Data.Options
import Lean.Widget
import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith

open Lean
open Lean Elab
open Lean Meta
open Lean.Elab.Tactic
open Lean Widget

def solvedEmoji := "✅"

-- should find all term info nodes which have no children
partial def findSubFrames (infoTree : InfoTree) : List String :=
  match infoTree with
  | InfoTree.node i children =>
    if children.size == 0 then
      match i with
      | .ofTermInfo _ => [s!"{i.stx.prettyPrint}"]
      | _ => []
    else
      children.map findSubFrames |>.toList.join
  | _ => []

structure Frame where
  fromType: String
  toType: String
  action: String
  subFrames : List String
  deriving ToJson

structure LetDefn where
  name : String
  defn: String
  deriving ToJson

structure TreeState where
  types : PersistentHashMap String String
  frames : List Frame
  defns : List LetDefn

instance : ToString Frame where
  toString f := s!"from: {f.fromType}, action: {f.action} to: {f.toType} subframes: {f.subFrames}"

abbrev FrameStack T := StateT TreeState IO T

def addFrame (frame : Frame) : FrameStack Unit :=
  modify fun state => {state with frames := frame :: state.frames }

def addDefn (name defn : String) : FrameStack Unit :=
  modify fun state => {state with defns := {name := name, defn := defn} :: state.defns }

def addName (name type : String) : FrameStack Unit :=
  modify fun state => {state with types := state.types.insert name type }

def isHaveTerm (info : Info) (children: PersistentArray InfoTree): Option TermInfo :=
  match info with
  | .ofTermInfo i => if s!"{i.stx.prettyPrint}".trimLeft.startsWith "let_fun" && children.size == 4 then i else none
  | _ => none

def isLetTerm(info : Info) : Bool :=
  match info with
  | .ofTermInfo i => s!"{i.stx.prettyPrint}".trimLeft.startsWith "let "
  | _ => false

def isTactic (names: List String) (info : Info) : Option (String × TacticInfo) := do
  match info with
  | .ofTacticInfo i => 
    for name in names do
      if s!"{i.elaborator}".trimRight.toLower.endsWith name then
        return (name, i)
    none
  | _ => none

def getGoalType (ctx: ContextInfo) (goals : List MVarId) (mctx : MetavarContext) : IO String :=
  if let some goal := goals.head? then
    if let some mDecl := mctx.findDecl? goal then
      ctx.runMetaM mDecl.lctx do return s!"{← ppExpr mDecl.type}"
    else panic! "goal is expected to be present in the metavar context"
  else pure solvedEmoji

def parseTacticProof (infoTree : InfoTree) : FrameStack Unit :=
  infoTree.visitM' fun (ctx : ContextInfo) (i: Info) (children : PersistentArray InfoTree) => do
    match i with
    | .ofTermInfo i =>
      match i.stx with
      | `(let_fun $name : $type := $d; $_) =>
        let name ← ctx.ppSyntax i.lctx name
        let type ← ctx.ppSyntax i.lctx type
        addName name.pretty type.pretty
        match d with
        | `(by $_) => pure ()
        | _ =>
          let dPretty ← ctx.ppSyntax i.lctx d
          let subFrames := findSubFrames children[1]!
          let t := {fromType := type.pretty, toType := solvedEmoji, action:= s!"exact {dPretty}", subFrames := subFrames}
          addFrame t
      | _ => pure ()
    | .ofTacticInfo tInfo =>
      match i.stx with
      | `(let $name := $defn ; $_ ) =>
        addDefn name.raw.prettyPrint.pretty defn.raw.prettyPrint.pretty
      | `(tactic| intro $name:ident) =>
        if let some goal := tInfo.goalsAfter.head? then
          if let some mDecl := tInfo.mctxAfter.findDecl? goal then
            if let some decl := mDecl.lctx.findFromUserName? name.getId then
              let introType ← ctx.runMetaM mDecl.lctx $ ppExpr decl.type
              addName name.raw.prettyPrint.pretty introType.pretty
          else panic! "goal is expected to be present in the metavar context"
        else panic! "after intro tactic there should be a goal"
        let fromType ← getGoalType ctx tInfo.goalsBefore tInfo.mctxBefore
        let toType ← getGoalType ctx tInfo.goalsAfter tInfo.mctxAfter
        addFrame {fromType,
                  toType,
                  action := s!"{i.stx.prettyPrint}",
                  subFrames := children.map (fun c => findSubFrames c) |>.toList.join}
      | `(tactic| apply $_)
      | `(tactic| exact $_)
      | `(tactic| refine $_)
      | `(tactic| linarith $_) =>
        let fromType ← getGoalType ctx tInfo.goalsBefore tInfo.mctxBefore
        let toType ← getGoalType ctx tInfo.goalsAfter tInfo.mctxAfter
        addFrame {fromType,
                  toType,
                  action := s!"{i.stx.prettyPrint}",
                  subFrames := children.map (fun c => findSubFrames c) |>.toList.join}
      | _ => pure ()
    | _ => pure ()

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

partial def ProofTree.format : ProofTree → MessageData
  | ProofTree.empty => "empty"
  | ProofTree.leaf f type => m!"{f}"
  | ProofTree.node f name ts =>
    MessageData.group $ printFrame f name
       ++ MessageData.nest 2 (Format.line ++ MessageData.ofList (ts.map ProofTree.format))
  where
    printFrame f name :=
      (if let some name := name then m!"{name}: " else "")
      ++ m!"{f.fromType} ====> {f.toType} : [[ {f.action} ]]"

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
    let (_, state ) ← (parseTacticProof tree).run ⟨ .empty, [], [] ⟩
    if let some type := getTopLevelType state then
      let state := {state with types := state.types.insert "top level" type}
      let fragments := findTree "top level" state
      return s!"{fragments.toJson}"
    else
      return "No top level type"

@[widget]
def ppWidget: UserWidgetDefinition := {
  name := "Paper proof"
  javascript:= include_str "widget" / "dist" / "paperProof.js"
}

-- TODOs
-- [Done] [P0] let definitions should be in the tree too
-- [Done] [P1] It would be also nice to print names before the type if we have them
-- [Done] [P1] Print as JSON so it can be used from TS
-- ==== Then draw that tree using TLDraw: Attempt 1 ============
-- [Done] [P2] We need types of intro'd names like `pln`
-- [P0] !!! I really need to rewrite the code so that it's more readable (see https://github.com/leanprover-community/mathlib4/pull/1218/files)
-- [P3] Definitions should be recursive too
-- ==== Then draw that tree using TLDraw: Attempt 2 ============
-- [P2] refine has ?_ in the type, we should replace it with the type of the mvar