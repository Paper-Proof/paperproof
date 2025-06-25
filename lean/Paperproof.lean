import Lean
import BetterParser
import CheckIfUserIsStillTyping
import Lean.Meta.Basic
import Lean.Elab.Tactic
open Lean Elab Meta Server RequestM

structure InputParams where
  pos : Lsp.Position
  mode: String
  deriving FromJson, ToJson

structure TheoremSignature where
  name : String
  signature : String
  deriving Inhabited, FromJson, ToJson

structure OutputParams where
  steps  : List ProofStep
  version: Nat
  theorems : List TheoremSignature := []
  deriving Inhabited, FromJson, ToJson

partial def getIds : Syntax → NameSet
  | .node _ _ args => (args.map getIds).foldl (·.append ·) {}
  | .ident _ _ nm _ => NameSet.empty.insert nm
  | _ => {}

def extractTheoremSignature (ctx : ContextInfo) (goalDecl : MetavarDecl) (name : Name) : RequestM (Option TheoremSignature) := do
  try
    let (constName, sigStr) ← ctx.runMetaM goalDecl.lctx do
      let resolvedName ← resolveGlobalConstNoOverloadCore name
      let constInfo ← getConstInfo resolvedName
      let lctx := goalDecl.lctx |>.sanitizeNames.run' {options := {}}
      let ppCtx := { (ctx.toPPContext lctx) with opts := (ctx.toPPContext lctx).opts.setBool `pp.fullNames true }
      let typeExpr ← ppExprWithInfos ppCtx constInfo.type
      let nameStr ← liftM (ppExprWithInfos ppCtx (mkConst constInfo.name))
      return (nameStr.fmt.pretty, typeExpr.fmt.pretty)
    return some { name := constName, signature := sigStr }
  catch _ => return none

@[server_rpc_method]
def getSnapshotData (params : InputParams) : RequestM (RequestTask OutputParams) := do
  withWaitFindSnapAtPos params.pos fun snap => do
    checkIfUserIsStillTyping snap params.pos
    if params.mode == "single_tactic" then
      let hoverPos := ((← readDoc).meta.text).lspPosToUtf8Pos params.pos
      let some tactic := (snap.infoTree.goalsAt? (← readDoc).meta.text hoverPos).head?
        | throwThe RequestError ⟨.invalidParams, "noGoalsAtResult"⟩
      let some ctx := Elab.Info.updateContext? tactic.ctxInfo (Elab.Info.ofTacticInfo tactic.tacticInfo)
        | throwThe RequestError ⟨.invalidParams, "couldntUpdateContext"⟩
      let some goalDecl := ctx.mctx.findDecl? tactic.tacticInfo.goalsBefore.head!
        | throwThe RequestError ⟨.invalidParams, "noGoalDecl"⟩
      
      let parsedTree ← parseTacticInfo ctx tactic.tacticInfo [] ∅
      let theorems ← (getIds tactic.tacticInfo.stx).toList.filterMapM (extractTheoremSignature ctx goalDecl)
      
      return { steps := parsedTree.steps, version := 3, theorems := theorems }
    else
      let some parsedTree ← BetterParser snap.infoTree
        | throwThe RequestError ⟨.invalidParams, "noParsedTree"⟩
      if parsedTree.steps.length == 0 then
        throwThe RequestError ⟨.invalidParams, "zeroProofSteps"⟩
      return { steps := parsedTree.steps, version := 3 }
