import Lean.Data.Json
import Lean.Elab.InfoTree
import Lean.Elab.Tactic

open Lean
open Lean.Elab
open Tactic

structure Hypothesis where
  username : String
  type : String
  value : Option String
  -- unique identifier for the hypothesis, fvarId
  id : String
  deriving Inhabited, ToJson

structure GoalInfo where
  type : String
  hyps : List Hypothesis 
  -- unique identifier for the goal, mvarId
  id : String
  deriving Inhabited, ToJson

structure TacticApplication where
  tacticString : String
  goalsBefore : List GoalInfo
  goalsAfter : List GoalInfo 
  tacticDependsOn : List String
  deriving Inhabited, ToJson

inductive ProofStep := 
  | tacticApp (t : TacticApplication)
  | haveDecl (name : String) (subSteps : List ProofStep)
  deriving Inhabited, ToJson

partial def findFVars (ctx: ContextInfo) (infoTree : InfoTree): List FVarId :=
  (InfoTree.context ctx infoTree).deepestNodes fun _ i _ =>
    match i with
    | .ofTermInfo ti  => if let .fvar id := ti.expr then some id else none
    | _ => none 

def getGoals (ctx : ContextInfo) (goals : List MVarId) (mctx : MetavarContext) : IO (List GoalInfo) := do
  goals.mapM fun id => do
    let some decl := mctx.findDecl? id
      | throw <| IO.userError "goal decl not found"
    let ppContext := ctx.toPPContext decl.lctx
    let hyps ← decl.lctx.foldlM (init := []) (fun acc decl => do
      if decl.isAuxDecl || decl.isImplementationDetail then
        return acc
      let type ← ppExprWithInfos ppContext decl.type
      let value ← decl.value?.mapM (ppExprWithInfos ppContext)
      return ({
        username := decl.userName.toString,
        type := type.fmt.pretty,
        value := value.map (·.fmt.pretty), 
        id := decl.fvarId.name.toString
        } : Hypothesis) ::acc)
    return ⟨ (← ppExprWithInfos ppContext decl.type).fmt.pretty, hyps, id.name.toString ⟩ 
  
partial def parse : (infoTree : InfoTree) → IO (List ProofStep) :=
  go none
where go
  | some ctx, .node i cs => do
    if let .ofTacticInfo tInfo := i then
      -- shortcut if it's not a tactic user wrote
      let some tacticString := tInfo.stx.getSubstring?.map (·.toString.trim)
        |  let as ← cs.toList.mapM (go <| i.updateContext? ctx)
           return as.join
      
      match tInfo.stx with
      | `(tactic| have $_:letPatDecl)
      | `(tactic| have $_ : $_ := $_) =>
        let as ← cs.toList.mapM (go <| i.updateContext? ctx)
        return [.haveDecl (tacticString.splitOn ":=" |>.head!.trim) as.join]
      | _ =>
        let as ← cs.toList.mapM (go <| i.updateContext? ctx) |>.map List.join
        if !as.isEmpty then
          -- If it's a tactic combinator, i.e. there are more granular tactics in the subtree,
          -- we return subtactic results instead.
          -- However we might need to prettify some results.
          match tInfo.stx with
          | `(tactic| rw [$_,*] $(_)?)
          | `(tactic| rewrite [$_,*] $(_)?) =>
            let prettify (tStr : String) :=
              let res := tStr.trim.dropRightWhile (· == ',')
              -- rw puts final rfl on the "]" token
              if res == "]" then "rfl" else res
            return as.map fun a => 
              match a with
              | .tacticApp a => .tacticApp { a with tacticString := s!"rw {prettify a.tacticString}" }
              | x => x
          | _ => return as

        -- Otherwise it's tactics like `apply`, `exact`, `simp`, etc.
        let some mainGoalDecl := tInfo.goalsBefore.head?.bind tInfo.mctxBefore.findDecl?
          | throw <| IO.userError "tactic applied to no goals"
        
        -- Find names to get decls
        let fvarIds := cs.toList.map (findFVars ctx) |>.join
        let fvars := fvarIds.filterMap mainGoalDecl.lctx.find?
          
        return [.tacticApp {
          tacticString,
          goalsBefore := ← getGoals ctx tInfo.goalsBefore tInfo.mctxBefore,
          goalsAfter := ← getGoals ctx tInfo.goalsAfter tInfo.mctxAfter,
          tacticDependsOn := fvars.map fun decl => s!"{decl.userName}"
          }]
    else
      let as ← cs.toList.mapM (go <| i.updateContext? ctx)
      return as.join
  | none, .node .. => panic! "unexpected context-free info tree node"
  | _, .context ctx t => go ctx t
  | _, .hole .. => pure []
    