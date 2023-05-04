import Lean.Data.Json
import Lean.Elab.InfoTree
import Mathlib.Tactic.Linarith

open Lean
open Lean.Elab

structure TacticApplication where
  tacticName : String
  goalsBefore : List String
  goalsAfter : List String
  tacticDependsOn : List String
  deriving Inhabited, ToJson

partial def parse : (infoTree : InfoTree) → IO (List TacticApplication) :=
  go none
where go
  | some ctx, .node i cs => do
    if let .ofTacticInfo tInfo := i then
      match tInfo.stx with
      | `(tactic| apply $_)
      | `(tactic| exact $_)
      | `(tactic| refine $_)
      | `(tactic| sorry)
      | `(tactic| linarith $_) =>
        let getGoals := fun (goals : List MVarId) (mctx : MetavarContext) =>
          goals.filterMap mctx.findDecl?
             |>.mapM fun decl => do
            let ppContext := ctx.toPPContext decl.lctx
            return (← ppExprWithInfos ppContext decl.type).fmt.pretty

        return [{
          tacticName := s!"{tInfo.stx}",
          goalsBefore := ← getGoals tInfo.goalsBefore tInfo.mctxBefore,
          goalsAfter := ← getGoals tInfo.goalsAfter tInfo.mctxAfter,
          tacticDependsOn := []
          }]
      | _ =>
        let as ← cs.toList.mapM (go <| i.updateContext? ctx)
        return as.join
    else
      let as ← cs.toList.mapM (go <| i.updateContext? ctx)
      return as.join
  | none, .node .. => panic! "unexpected context-free info tree node"
  | _, .context ctx t => go ctx t
  | _, .hole .. => pure []
    