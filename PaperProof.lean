import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith
import Std.Classes.Dvd
import Lean.Elab.Tactic
import Lean
import Lean.Environment
import Lean.Elab.Frontend
import Lean.Elab.InfoTree
import Lean.Data.Options
import Lean.Widget

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

def goDeeper (info : Info) : Bool :=
  match info with
  | .ofTacticInfo i => 
    if s!"{i.stx.prettyPrint}".startsWith "let" then
      false
    else
      true
  | _ => true

def isSameSpan (infoTree : InfoTree) (fromPos toPos : String.Pos) : Bool :=
  match infoTree with
  | InfoTree.node i _ =>
    let fromPos' := i.stx.getPos?.get!
    let toPos' := i.stx.getTailPos?.get!
    fromPos == fromPos' && toPos == toPos'
  | _ => false

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

def isHaveTerm (info : Info) (children: PersistentArray InfoTree): Bool :=
  match info with
  | .ofTermInfo i => s!"{i.stx.prettyPrint}".trimLeft.startsWith "let_fun" && children.size == 4
  | _ => false

def isLetTerm(info : Info) (children: PersistentArray InfoTree): Bool :=
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

structure Goals where
  goalsBefore : List MVarId
  goalsAfter : List MVarId
  deriving ToJson

partial def getLCtx (info : Info) (children : PersistentArray InfoTree): Option LocalContext :=
  match info with
  | .ofTermInfo i => i.lctx
  | .ofMacroExpansionInfo i => i.lctx
  | .ofFieldInfo i => i.lctx
  | .ofTacticInfo i => if children.size > 0 then
    -- call recursively because for example on `intro N` we had not term above to set the context.
    match children[0]! with
      | .node ii cs => getLCtx ii cs
      | _ => none
    else none
  | _ => none

def getType (ctx: Option ContextInfo) (lctx : Option LocalContext) (tInfo: TacticInfo) (before := false) : FrameStack String :=
  let goals := if before then tInfo.goalsBefore else tInfo.goalsAfter
  let lctx := lctx.getD {}
  if let (some context) := (ctx) then
    if goals.length > 0 then
      context.runMetaM lctx $ do
        let mvar := goals[0]!
        let type ← mvar.getType
        return s!"{← ppExpr type}"
    else pure solvedEmoji
  else pure solvedEmoji


partial def parseTacticProof (ctx : Option ContextInfo) (lctx : Option LocalContext) (infoTree : InfoTree) (name: String := "top level") : FrameStack MessageData := do
  match infoTree with
  | InfoTree.node i children =>
    let lctx := if let some c := getLCtx i children then c else lctx
    let fromPos := i.stx.getPos?.get!
    let toPos := i.stx.getTailPos?.get!

    let processTactic (tacticName : String) (tInfo : TacticInfo) : FrameStack MessageData := do
      let subFrames := children.map (fun c => findSubFrames c) |>.toList.join
      let type ← getType ctx lctx tInfo
      let beforeGoal ← getType ctx lctx tInfo true
      let t := {
        fromType := beforeGoal,
        toType := type,
        action := s!"{i.stx.prettyPrint}",
        subFrames := subFrames}
      addFrame t
      let info := m!"!!!! {tInfo.elaborator} {tacticName} {i.stx.prettyPrint}"
      let cs := (← children.mapM (parseTacticProof ctx lctx)) |>.toList
      return MessageData.group $ info ++ MessageData.nest 2 (Format.line ++ MessageData.ofList cs)

    if children.size == 1 && isSameSpan children[0]! fromPos toPos then
      parseTacticProof ctx lctx children[0]! -- this is helpful only for tree output, not parsing
    else if children.size == 2 && i.stx.prettyPrint.pretty.trimLeft.startsWith "focus" then
      parseTacticProof ctx lctx children[1]! -- same as above
    else if isLetTerm i children then
      -- Here I somehow need to extract the name and definition and subterms
      let name := toStrSyntax children[2]!
      let defn := toStrSyntax children[1]!
      addDefn name defn
      let info := printInfo i
      let cs := (← children.mapM (parseTacticProof ctx lctx)) |>.toList
      return MessageData.group $ info ++ MessageData.nest 2 (Format.line ++ MessageData.ofList cs)
    else if isHaveTerm i children then
      -- let type := getType ctx lctx i
      let vals ← children.mapM (fun c => toStrType c ctx lctx)
      let name := toStrSyntax children[2]!
      addName name vals[0]!
      if vals[1]!.trimLeft.startsWith "by" then
        let info := "BBB" ++ printInfo i
        let r ← parseTacticProof ctx lctx children[1]!
        return info ++ r
      else
        let subFrames := findSubFrames children[1]!
        let t := {fromType := vals[0]!, toType := solvedEmoji, action:= s!"exact {vals[1]!}", subFrames := subFrames}
        addFrame t
        let info := m!"Parsed have {t.subFrames}: type: {t.toType}, action: {t.action}"
        return info
    else if let some ⟨ tName, tInfo ⟩ := isTactic ["apply", "exact", "intro", "refine", "linarith_1"] i then
      processTactic tName tInfo
    else
      let info := printInfo i
      let cs := (← children.mapM (parseTacticProof ctx lctx)) |>.toList
      return MessageData.group $ info ++ MessageData.nest 2 (Format.line ++ MessageData.ofList cs)
  | InfoTree.context ctx t => parseTacticProof ctx lctx t 
  | _ => return m!"+++++++"

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
  | leaf : String → ProofTree
  | node : Frame → Option String → List ProofTree → ProofTree
  deriving Inhabited

partial def ProofTree.format : ProofTree → MessageData
  | ProofTree.empty => "empty"
  | ProofTree.leaf f => m!"{f}"
  | ProofTree.node f name ts =>
    MessageData.group $ printFrame f name
       ++ MessageData.nest 2 (Format.line ++ MessageData.ofList (ts.map ProofTree.format))
  where
    printFrame f name :=
      (if let some name := name then m!"{name}: " else "")
      ++ m!"{f.fromType} ====> {f.toType} : [[ {f.action} ]]"

partial def findTree (name : String) (state : TreeState): ProofTree :=
  if name == solvedEmoji then
    .leaf name
  else
    let type := state.types.findD name name
    if let some frame := state.frames.find? (fun f => f.fromType == type) then
      let subTrees := frame.subFrames.map (fun f => findTree f state)
      .node frame
        (if type != name then name else none)
        ((findTree frame.toType state) :: subTrees)
    else if let some d := state.defns.find? (fun f => f.name == name) then
      .leaf s!"{d.name} := {d.defn}"
    else 
      .leaf type

elab "#buildTree" : command => do
  let filename := "Example.lean"
  let content ← IO.FS.readFile filename
  let opts := Options.empty
  let inputCtx := Parser.mkInputContext content filename
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header opts messages inputCtx 0
  let env := env.setMainModule `Init
  let mut commandState := Command.mkState env messages opts

  let s ← IO.processCommands inputCtx parserState { commandState with infoState.enabled := true }
  for msg in s.commandState.messages.toList do
    IO.print (← msg.toString (includeEndPos := getPrintMessageEndPos opts))
  let tree := s.commandState.infoState.trees[0]!
  let (pp, state ) ← (parseTacticProof none none tree).run ⟨ .empty, [], [] ⟩
  let env := s.commandState.env
  let expr := (env.find? `infinitude_of_primes).get!.toConstantVal.type
  let type ← if let (.context ctx _) := tree then ctx.runMetaM {} (ppExpr expr) else return ()
  let state := {state with types := state.types.insert "top level" s!"{type}"}
  let fragments := findTree "top level" state
  logInfo m!"{fragments.format}"
--   logInfo "----------------"
--  for (name, type) in types.toList do
--    logInfo s!"{name} : {type}"
  logInfo "----------------"
  for frame in state.frames do
    logInfo s!"{frame}"
  logInfo pp

#buildTree

-- TODOs
-- [Done] [P0] let definitions should be in the tree too
-- [Done] [P1] It would be also nice to print names before the type if we have them
-- [P1] Print as JSON so it can be used from TS
-- ==== Then draw that tree using TLDraw ============
-- [P2] We need types of intro'd names like `pln`
-- [P2] refine has ?_ in the type, we should replace it with the type of the mvar
-- [P3] Definitions should be recursive too