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
  username : String
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
  | haveDecl (t: TacticApplication)
    (initialGoal: String)
    (subSteps : List ProofStep)
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
    -- to get tombstones in name ✝ for unreachable hypothesis
    let lctx := decl.lctx |>.sanitizeNames.run' {options := {}}
    let hyps ← lctx.foldlM (init := []) (fun acc decl => do
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
    return ⟨ decl.userName.toString, (← ppExprWithInfos ppContext decl.type).fmt.pretty, hyps, id.name.toString ⟩

structure Proof where
  statement : String
  steps : List ProofStep
  deriving Inhabited, ToJson 

def getInitialGoal (steps: List ProofStep) : Option String :=
  let goals := match steps.head? with
    | .none => []
    | .some (.tacticApp t) => t.goalsBefore
    | .some (.haveDecl t _ _) => t.goalsBefore
  goals.head?.bind fun g => g.type
  
partial def parse (infoTree : InfoTree) : IO Proof := do
  let steps ← go none infoTree
  let some statement := getInitialGoal steps 
    | throw <| IO.userError "initial goal is expected for theorem"
  return {statement, steps}
where go
  | some ctx, .node i cs => do
    let as ← cs.toList.mapM (go <| i.updateContext? ctx) |>.map List.join
    if let .ofTacticInfo tInfo := i then
      -- shortcut if it's not a tactic user wrote
      -- \n trim to avoid empty lines/comments until next tactic,
      -- especially at the end of theorem it will capture comment for the next one
      let some tacticString := tInfo.stx.getSubstring?.map
            (·.toString |>.splitOn "\n" |>.head!.trim)
        | return as
      let some mainGoalDecl := tInfo.goalsBefore.head?.bind tInfo.mctxBefore.findDecl?
        -- For example a tactic like `done` just ensures there are no unsolved goals,
        -- however has no information for the tactic tree
        | return as
      
      -- Find names to get decls
      let fvarIds := cs.toList.map (findFVars ctx) |>.join
      let fvars := fvarIds.filterMap mainGoalDecl.lctx.find?
      let tacticApp: TacticApplication := {
          tacticString,
          goalsBefore := ← getGoals ctx tInfo.goalsBefore tInfo.mctxBefore,
          goalsAfter := ← getGoals ctx tInfo.goalsAfter tInfo.mctxAfter,
          tacticDependsOn := fvars.map fun decl => s!"{decl.fvarId.name.toString}"
          }
      if as.isEmpty then
        -- When `as` is non-empty it's a tactic combinator, i.e. there are more granular tactics
        -- in the subtree. For example `have` with `by` or `rw [a,b]`
        -- Otherwise it's a tactic like `apply`, `exact`, `simp`, or a simple `have` defined in term mode etc.
        return [.tacticApp tacticApp]
      
      -- It's a tactic combinator
      match tInfo.stx with
      -- TODO: can we grab all have's as one pattern match branch?
      | `(tactic| have $_:letPatDecl)
      | `(tactic| have $_ : $_ := $_) =>
        let some initialGoal := getInitialGoal as
          | throw <| IO.userError "initial goal is expected for have"
        return [.haveDecl
                    tacticApp
                    initialGoal
                    as]
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
    else
      return as
  | none, .node .. => panic! "unexpected context-free info tree node"
  | _, .context ctx t => go ctx t
  | _, .hole .. => pure []
    