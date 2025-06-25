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

structure ArgumentInfo where
  name : String
  type : String
  deriving Inhabited, FromJson, ToJson

structure TheoremSignature where
  name : String
  signature : String
  instanceArgs : List ArgumentInfo := []   -- []
  implicitArgs : List ArgumentInfo := []   -- {}
  explicitArgs : List ArgumentInfo := []   -- ()
  body : String := ""                      -- return type
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

def getAllArgsWithTypes (expr : Expr) : MetaM (List ArgumentInfo × List ArgumentInfo × List ArgumentInfo × String) := do
  Meta.forallTelescope expr fun args body => do
    let mut lctx := LocalContext.empty
    for arg in args do
      let decl ← arg.fvarId!.getDecl
      lctx := lctx.addDecl decl
    
    let ppCtx : PPContext := { 
      env := ← getEnv, 
      mctx := ← getMCtx, 
      lctx, 
      opts := (← getOptions).setBool `pp.fullNames true 
    }
    
    let mut instanceArgs := []
    let mut implicitArgs := []
    let mut explicitArgs := []
    
    for arg in args do
      let decl ← arg.fvarId!.getDecl
      let typeStr ← ppExprWithInfos ppCtx decl.type
      let argInfo := { name := decl.userName.toString, type := typeStr.fmt.pretty : ArgumentInfo }
      
      match decl.binderInfo with
      | BinderInfo.instImplicit => instanceArgs := instanceArgs ++ [argInfo]
      | BinderInfo.implicit => implicitArgs := implicitArgs ++ [argInfo]
      | BinderInfo.strictImplicit => implicitArgs := implicitArgs ++ [argInfo]
      | BinderInfo.default => explicitArgs := explicitArgs ++ [argInfo]
    
    let bodyStr ← ppExprWithInfos ppCtx body
    return (instanceArgs, implicitArgs, explicitArgs, bodyStr.fmt.pretty)

def extractTheoremSignature (ctx : ContextInfo) (goalDecl : MetavarDecl) (name : Name) : RequestM (Option TheoremSignature) := do
  try
    ctx.runMetaM goalDecl.lctx do
      let resolvedName ← resolveGlobalConstNoOverloadCore name
      let constInfo ← getConstInfo resolvedName
      let ppCtx := { (ctx.toPPContext (goalDecl.lctx |>.sanitizeNames.run' {options := {}})) with 
                     opts := (ctx.toPPContext goalDecl.lctx).opts.setBool `pp.fullNames true }
      
      let nameStr ← liftM (ppExprWithInfos ppCtx (mkConst constInfo.name))
      let typeExpr ← ppExprWithInfos ppCtx constInfo.type
      let (instanceArgs, implicitArgs, explicitArgs, body) ← getAllArgsWithTypes constInfo.type
      
      return some { 
        name := nameStr.fmt.pretty, 
        signature := typeExpr.fmt.pretty, 
        instanceArgs,
        implicitArgs,
        explicitArgs,
        body
      }
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
      return { steps := parsedTree.steps, version := 3, theorems }
    else
      let some parsedTree ← BetterParser snap.infoTree
        | throwThe RequestError ⟨.invalidParams, "noParsedTree"⟩
      if parsedTree.steps.length == 0 then
        throwThe RequestError ⟨.invalidParams, "zeroProofSteps"⟩
      return { steps := parsedTree.steps, version := 3 }
