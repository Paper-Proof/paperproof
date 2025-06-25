import Lean

import BetterParser

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
  match expr.consumeMData with
  | .const name _ => some name
  | .app .. => expr.getAppFn.consumeMData.constName?
  | .fvar .. => do
    let ldecl ← lctx.findFVar? expr
    let val ← ldecl.value?
    val.getAppFn.consumeMData.constName?
  | _ => none

/-- Finds theorem names within a specific source code range (for filtering to user-written code only) -/
def findTheoremsInTacticRange (tree : Elab.InfoTree) (tacticStartPos tacticStopPos : String.Pos) : List Name :=
  tree.deepestNodes fun _ info _ => do
    let .ofTermInfo ti := info | none
    let substr ← ti.stx.getSubstring?
    guard (isInRange substr tacticStartPos tacticStopPos)
    extractTheoremName ti.expr ti.lctx

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
  catch _ => return none


def GetTheoremsUsedInTactic (infoTree : InfoTree) (tacticInfo : TacticInfo) (ctx : ContextInfo) : RequestM (List TheoremSignature) := do
  let some goalDecl := ctx.mctx.findDecl? tacticInfo.goalsBefore.head!
        | throwThe RequestError ⟨.invalidParams, "noGoalDecl"⟩
  let some tacticSubstring := getTacticSubstring tacticInfo
        | throwThe RequestError ⟨.invalidParams, "xxx"⟩
  let theorems := findTheoremsInTacticRange infoTree tacticSubstring.startPos tacticSubstring.stopPos
  theorems.filterMapM (extractTheoremSignature ctx goalDecl)
