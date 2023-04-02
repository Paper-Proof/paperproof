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

def printInfo (info : Info) (printAll : Bool) : MessageData :=
  match info with
  | .ofTacticInfo ti => 
    if ti.stx.prettyPrint.pretty.startsWith "have" then
      m!"TCTCINFO {ti.stx.prettyPrint}"
    else
      if printAll then m!"tactic info ${ti.elaborator} ${info.stx.getPos?}, {info.stx.getTailPos?} <{ti.stx.prettyPrint}>" else m!""
  | .ofTermInfo i => if printAll then m!"term info {info.stx.prettyPrint}" else m!""
  | .ofCommandInfo _ => if printAll then m!"command info {info.stx.prettyPrint}" else m!""
  | .ofMacroExpansionInfo _ => m!"macro expansion info"
  | .ofFieldInfo _ => m!"field info"
  | .ofCompletionInfo _ => m!"completion info"
  | .ofCustomInfo _ => m!"custom info"
  | _ => if printAll then m!"other info" else m!""

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

structure TreeState where
  types : PersistentHashMap String String
  frames : List Frame

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

def addName (name type : String) : FrameStack Unit :=
  modify fun state => {state with types := state.types.insert name type }

def isHaveTerm (info : Info) (children: PersistentArray InfoTree): Bool :=
  match info with
  | .ofTermInfo i => s!"{i.stx.prettyPrint}".trimLeft.startsWith "let_fun" && children.size == 4
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
    else if isHaveTerm i children then
      -- let type := getType ctx lctx i
      let vals ← children.mapM (fun c => toStrType c ctx lctx)
      let name := toStrSyntax children[2]!
      addName name vals[0]!
      if vals[1]!.trimLeft.startsWith "by" then
        let info := "BBB" ++ printInfo i true
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
      let info := printInfo i true
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
  let (pp, ⟨ types, frames ⟩ ) ← (parseTacticProof none none tree).run ⟨ .empty, [] ⟩
  let env := s.commandState.env
  let expr := (env.find? `infinitude_of_primes).get!.toConstantVal.type
  let type ← if let (.context ctx _) := tree then ctx.runMetaM {} (ppExpr expr) else return ()
  let types := types.insert "top level" s!"{type}"
  let fragments := findChain "h₂" types frames
  for frag in fragments do
    logInfo s!"{frag}"
  logInfo "----------------"
  for (name, type) in types.toList do
    logInfo s!"{name} : {type}"
  logInfo "----------------"
  for frame in frames do
    logInfo s!"{frame}"
  logInfo pp

#buildTree