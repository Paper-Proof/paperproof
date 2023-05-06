import Lean.Data.Json
import Lean.Elab.InfoTree
import Lean.Elab.Tactic
import Mathlib.Tactic.Linarith

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

partial def findFVars (ctx: ContextInfo) (infoTree : InfoTree): List FVarId :=
  (InfoTree.context ctx infoTree).deepestNodes fun _ i _ =>
    match i with
    | .ofTermInfo ti  => if let .fvar id := ti.expr then some id else none
    | _ => none 

partial def parse : (infoTree : InfoTree) → IO (List TacticApplication) :=
  go none
where go
  | some ctx, .node i cs => do
    if let .ofTacticInfo tInfo := i then
      let getGoals := fun (goals : List MVarId) (mctx : MetavarContext) =>
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

      -- shortcut if it's not a tactic user wrote
      let some tacticString := tInfo.stx.getSubstring?.map (·.toString.trim)
        |  let as ← cs.toList.mapM (go <| i.updateContext? ctx)
           return as.join
      
      match tInfo.stx with
      | `(tactic| apply $_)
      | `(tactic| exact $_)
      | `(tactic| refine $_)
      | `(tactic| sorry)
      | `(tactic| linarith)
      | `(tactic| rw [$_] at $_)
      | `(tactic| intro $_:ident) =>
        let some mainGoalDecl := tInfo.goalsBefore.head?.bind tInfo.mctxBefore.findDecl?
          | throw <| IO.userError "tactic applied to no goals"
        
        -- Find names to get decls
        let fvarIds := cs.toList.map (findFVars ctx) |>.join
        let fvars := fvarIds.filterMap mainGoalDecl.lctx.find?
          
        return [{
          tacticString,
          goalsBefore := ← getGoals tInfo.goalsBefore tInfo.mctxBefore,
          goalsAfter := ← getGoals tInfo.goalsAfter tInfo.mctxAfter,
          tacticDependsOn := fvars.map fun decl => s!"{decl.userName}"
          }]
      | `(tactic| have $name : $_ := $_) =>
        let as ← cs.toList.mapM (go <| i.updateContext? ctx)
        return {
          tacticString := s!"have {name.getId}",
          goalsBefore := ← getGoals tInfo.goalsBefore tInfo.mctxBefore,
          goalsAfter := ← getGoals tInfo.goalsAfter tInfo.mctxAfter,
          tacticDependsOn := []
          } :: as.join
      | _ =>
        let as ← cs.toList.mapM (go <| i.updateContext? ctx)
        return as.join
    else
      let as ← cs.toList.mapM (go <| i.updateContext? ctx)
      return as.join
  | none, .node .. => panic! "unexpected context-free info tree node"
  | _, .context ctx t => go ctx t
  | _, .hole .. => pure []
    