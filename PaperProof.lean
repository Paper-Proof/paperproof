import Lean.Elab.Tactic
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

def printInfo (info : Info) : MessageData :=
  match info with
  | .ofTacticInfo ti => 
    if ti.stx.prettyPrint.pretty.startsWith "have" then
      m!"TCTCINFO {ti.stx.prettyPrint}"
    else
      m!"tactic info ${ti.elaborator} ${info.stx.getPos?}, {info.stx.getTailPos?} <{ti.stx.prettyPrint}>"
  | .ofTermInfo i => m!"term info {info.stx.prettyPrint}"
  | .ofCommandInfo _ => m!"command info {info.stx.prettyPrint}"
  | .ofMacroExpansionInfo _ => m!"macro expansion info"
  | .ofFieldInfo _ => m!"field info"
  | .ofCompletionInfo _ => m!"completion info"
  | .ofCustomInfo _ => m!"custom info"
  | _ => m!"other info"

-- should find all term info nodes which have no children
partial def findSubFrames (infoTree : InfoTree) : List String :=
  match infoTree with
  | InfoTree.node i children =>
    if children.size == 0 then
      match i with
      | .ofTermInfo info => [s!"{i.stx.prettyPrint}"]
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

def toStrType (infoTree : InfoTree) (ctx : Option ContextInfo) (lctx : Option LocalContext) : FrameStack String := do
  if let some ctx := ctx then
    match infoTree with
    | InfoTree.node (.ofTermInfo i) _ => ctx.runMetaM (lctx.getD {}) $ do
      return s!"{← ppExpr i.expr}"
    | InfoTree.node i _ => return s!"{i.stx.prettyPrint}"
    | _ => return s!""
  else return "XXX"

def toStrSyntax (infoTree : InfoTree) : String :=
  match infoTree with
  | InfoTree.node i _ => s!"{i.stx.prettyPrint}"
  | _ => s!""

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

def getType (ctx: ContextInfo) (goals : List MVarId) (mctx : MetavarContext) : FrameStack String :=
  if let some goal := goals.head? then
    if let some mDecl := mctx.findDecl? goal then
      ctx.runMetaM mDecl.lctx do return s!"{← ppExpr mDecl.type}"
    else panic! "goal is expected to be in metavar context"
  else pure solvedEmoji

def parseTacticProof (infoTree : InfoTree) : FrameStack Unit :=
  infoTree.visitM' fun (ctx : ContextInfo) (i: Info) (children : PersistentArray InfoTree) => do
    let processTactic (tInfo : TacticInfo) : FrameStack Unit := do
      let subFrames := children.map (fun c => findSubFrames c) |>.toList.join
      let type ← getType ctx tInfo.goalsAfter tInfo.mctxAfter
      let beforeGoal ← getType ctx tInfo.goalsBefore tInfo.mctxBefore
      let t := {
        fromType := beforeGoal,
        toType := type,
        action := s!"{i.stx.prettyPrint}",
        subFrames := subFrames}
      addFrame t

    if isLetTerm i then
      -- Here I somehow need to extract the name and definition and subterms
      let name := toStrSyntax children[2]!
      let defn := toStrSyntax children[1]!
      addDefn name defn
    else if let some ti := isHaveTerm i children then
      -- let type := getType ctx lctx i
      let vals ← children.mapM (fun c => toStrType c ctx ti.lctx)
      let name := toStrSyntax children[2]!
      addName name vals[0]!
      if !vals[1]!.trimLeft.startsWith "by" then
        let subFrames := findSubFrames children[1]!
        let t := {fromType := vals[0]!, toType := solvedEmoji, action:= s!"exact {vals[1]!}", subFrames := subFrames}
        addFrame t
    else if let some ⟨ tName, tInfo ⟩ := isTactic ["apply", "exact", "intro", "refine", "linarith_1"] i then
      if tName == "intro" then
        if let InfoTree.node (.ofTermInfo i) _ := children[0]! then
          let type ← ctx.runMetaM i.lctx do
            let t ← inferType i.expr
            ppExpr t
          addName (toStrSyntax children[0]!) s!"{type}"
      processTactic tInfo


-- Questions:
-- 1) How to get a source code for the definiton?

partial def findChain (name : String) (types : PersistentHashMap String String) (frames : List Frame): List Frame := Id.run do
  if name == solvedEmoji then
    []
  else
    let type := types.findD name name
    for frame in frames do
      if frame.fromType == type then
        return frame :: findChain frame.toType types frames
    []
  
inductive ProofTree where
  | empty : ProofTree 
  -- Name and type of the leaf
  | leaf : String → String →  ProofTree
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

def ppExpr' := Lean.Meta.MetaM.run' ∘ ppExpr

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

#widget ppWidget .null

-- #explode infinitude_of_primes

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