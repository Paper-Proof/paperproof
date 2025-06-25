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

/-- Finds theorems within a specific source code range (for filtering to user-written code only) -/
def findTheoremsInTacticRange (tree : Elab.InfoTree) (tacticStartPos tacticStopPos : String.Pos) : Array (Name × Elab.TermInfo) :=
  let nodes := tree.deepestNodes (fun ctx info children =>
    match info with
    | Elab.Info.ofTermInfo ti =>
      -- Check if this term's position is within the tactic range
      
      if let some substr := ti.stx.getSubstring? then
        -- Check if this term's position is within the tactic range
        if substr.startPos >= tacticStartPos && substr.stopPos <= tacticStopPos then
          -- Continue with the existing logic
          if ti.expr.isSyntheticSorry then none
          else
            match ti.expr.consumeMData with
            | .const name _ => some (name, ti)
            | .app .. =>
              let name? := Expr.getAppFn ti.expr |>.consumeMData |>.constName?
              name?.map fun name => (name, ti)
            | .fvar .. =>
              if let some ldecl := ti.lctx.findFVar? ti.expr then
                if let some val := ldecl.value? then
                  let name? := Expr.getAppFn val |>.consumeMData |>.constName?
                  name?.map fun name => (name, ti)
                else none
              else none
            | _ => none
        else none

      else none
    | _ => none) |>.toArray
  nodes

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
def extractTheoremSignature (ctx : ContextInfo) (goalDecl : MetavarDecl) (nameAndTerm : Name × Elab.TermInfo) : RequestM (Option TheoremSignature) := do
  let (name, termInfo) := nameAndTerm
  try
    ctx.runMetaM goalDecl.lctx do
      let resolvedName ← resolveGlobalConstNoOverloadCore name
      let constInfo ← getConstInfo resolvedName
      
      -- Only process declarations that might be useful as theorems (skip pure constructors, etc.)
      -- if constInfo.isConstructor && !constInfo.type.isProp && !constInfo.type.hasArrow then
      --   return none
        
      let ppCtx := { (ctx.toPPContext (goalDecl.lctx |>.sanitizeNames.run' {options := {}})) with 
                     opts := (ctx.toPPContext goalDecl.lctx).opts.setBool `pp.fullNames true }
      
      -- If we have a term info, we can get more precise information about the expression
      let expr := termInfo.expr
      
      -- Get documentation if available
      let docString? ← findDocString? (ctx.env) resolvedName
      
      -- Use ppSignature for constants when possible (similar to Lean's hover)
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
      
      -- Get the tactic's source code range and filter theorems to that range
      let theorems ← 
        if let some tacticSubstring := getTacticSubstring tactic.tacticInfo then
          findTheoremsInTacticRange snap.infoTree tacticSubstring.startPos tacticSubstring.stopPos
          |> Array.toList |>.filterMapM (extractTheoremSignature ctx goalDecl)
        else
          pure []

      return { steps := parsedTree.steps, version := 3, theorems }
    else
      let some parsedTree ← BetterParser snap.infoTree
        | throwThe RequestError ⟨.invalidParams, "noParsedTree"⟩
      if parsedTree.steps.length == 0 then
        throwThe RequestError ⟨.invalidParams, "zeroProofSteps"⟩
      return { steps := parsedTree.steps, version := 3 }
