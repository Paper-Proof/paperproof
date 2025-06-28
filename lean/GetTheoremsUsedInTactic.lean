import Lean
import GetTacticSubstring
open Lean Elab Server

structure ArgumentInfo where
  name : String
  type : String
  deriving Inhabited, FromJson, ToJson

structure TheoremSignature where
  name         : String
  instanceArgs : List ArgumentInfo := [] -- []
  implicitArgs : List ArgumentInfo := [] -- {}
  explicitArgs : List ArgumentInfo := [] -- ()
  body         : String := ""            -- return type
  deriving Inhabited, FromJson, ToJson

partial def getIds : Syntax → NameSet
  | .node _ _ args => (args.map getIds).foldl (·.append ·) {}
  | .ident _ _ nm _ => NameSet.empty.insert nm
  | _ => {}

/-- Check if a substring position is within a given range -/
def isInRange (substr : Substring) (startPos stopPos : String.Pos) : Bool :=
  substr.startPos >= startPos && substr.stopPos <= stopPos

/-- Extract theorem name from expression, handling constants, applications, and local variables -/
def extractTheoremName (expr : Expr) (lctx : LocalContext) : Option Name := do
  guard (!expr.isSyntheticSorry)
  -- It's important to use cleanExpr here, otherwise we'll be getting "fvar expected" exceptions sometimes
  let cleanExpr := expr.consumeMData
  match cleanExpr with
  | .const name _ => some name
  | .app .. => expr.getAppFn.consumeMData.constName?
  | .fvar .. => do
    let ldecl ← lctx.findFVar? cleanExpr
    let val ← ldecl.value?
    val.getAppFn.consumeMData.constName?
  | _ => none

/-- Finds unique fully qualified theorem names within a specific source code range -/
def findTheoremsInTacticRange (tree : Elab.InfoTree) (tacticStartPos tacticStopPos : String.Pos) : MetaM (List Name) := do
  -- 1. Extract theorem names from tactic
  let rawNames := tree.deepestNodes fun _ info _ => do
    let .ofTermInfo ti := info | none
    -- let substr ← ti.stx.getSubstring?
    -- Guarding this misses some lemmas
    -- guard (isInRange substr tacticStartPos tacticStopPos)
    extractTheoremName ti.expr ti.lctx

  -- 2. Make theorem names fully qualified
  let resolvedNames : List Name ← rawNames.mapM resolveGlobalConstNoOverloadCore

  -- 3. Remove duplicates
  pure resolvedNames.toSSet.toList

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

def extractTheoremSignature (ctx : ContextInfo) (goalDecl : MetavarDecl) (name : Name) : MetaM (Option TheoremSignature) := do
  let constInfo ← getConstInfo name

  let ppCtx := { (ctx.toPPContext (goalDecl.lctx |>.sanitizeNames.run' {options := {}})) with opts := (ctx.toPPContext goalDecl.lctx).opts.setBool `pp.fullNames true }

  -- Use ppSignature for constants when possible (similar to Lean's hover)
  let nameStr ← liftM (ppExprWithInfos ppCtx (mkConst constInfo.name))
  let (instanceArgs, implicitArgs, explicitArgs, body) ← getAllArgsWithTypes constInfo.type
  
  return some { 
    name := nameStr.fmt.pretty,
    instanceArgs,
    implicitArgs,
    explicitArgs,
    body
  }

def GetTheoremsUsedInTactic (infoTree : InfoTree) (tacticInfo : TacticInfo) (ctx : ContextInfo) : RequestM (List TheoremSignature) := do
  let some goalDecl := ctx.mctx.findDecl? tacticInfo.goalsBefore.head!
    | throwThe RequestError ⟨.invalidParams, "noGoalDecl"⟩
  let some tacticSubstring := getTacticSubstring tacticInfo
    | throwThe RequestError ⟨.invalidParams, "noTacticSubstring"⟩

  ctx.runMetaM goalDecl.lctx do
    let theoremNames ← findTheoremsInTacticRange infoTree tacticSubstring.startPos tacticSubstring.stopPos
    theoremNames.filterMapM (extractTheoremSignature ctx goalDecl)
  