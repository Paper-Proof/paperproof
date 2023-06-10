import Lean.Data.Json
import Lean.Data.HashSet
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
    -- to get tombstones in name ✝ for unreachable hypothesis
    let lctx := decl.lctx |>.sanitizeNames.run' {options := {}}
    let ppContext := ctx.toPPContext lctx
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

structure Result where
  steps : List ProofStep
  goalsBefore : List GoalInfo
  goalsAfter : List GoalInfo

partial def parse (infoTree : InfoTree) : IO Proof := do
  let result ← (go none infoTree : IO Result)
  let some statement := getInitialGoal result.steps 
    | throw <| IO.userError "initial goal is expected for theorem"
  return {statement, steps := result.steps}
where go
  | some (ctx : ContextInfo), .node i cs => do
    let newCtx := i.updateContext? ctx
    let res ← cs.toList.mapM (go newCtx)
    let as := res.map (fun r => r.steps) |>.join
    if let .ofTacticInfo tInfo := i then
      let goalsBefore ← getGoals ctx tInfo.goalsBefore tInfo.mctxBefore
      let goalsAfter ← getGoals ctx tInfo.goalsAfter tInfo.mctxAfter
      let result : Result := {steps := as, goalsBefore, goalsAfter}
      -- shortcut if it's not a tactic user wrote
      -- \n trim to avoid empty lines/comments until next tactic,
      -- especially at the end of theorem it will capture comment for the next one
      let some tacticString := tInfo.stx.getSubstring?.map
            (·.toString |>.splitOn "\n" |>.head!.trim)
        | return result
      let some mainGoalDecl := tInfo.goalsBefore.head?.bind tInfo.mctxBefore.findDecl?
        -- For example a tactic like `done` just ensures there are no unsolved goals,
        -- however has no information for the tactic tree
        | return result
      
      -- Find names to get decls
      let fvarIds := cs.toList.map (findFVars ctx) |>.join
      let fvars := fvarIds.filterMap mainGoalDecl.lctx.find?
      let tacticApp: TacticApplication := {
          tacticString,
          goalsBefore,
          goalsAfter,
          tacticDependsOn := fvars.map fun decl => s!"{decl.fvarId.name.toString}"
          }
      if as.isEmpty then
        -- When `as` is non-empty it's a tactic combinator, i.e. there are more granular tactics
        -- in the subtree. For example `have` with `by` or `rw [a,b]`
        -- Otherwise it's a tactic like `apply`, `exact`, `simp`, or a simple `have` defined in term mode etc.
        return {result with steps := [.tacticApp tacticApp]} 
      
      -- It's a tactic combinator
      match tInfo.stx with
      -- TODO: can we grab all have's as one pattern match branch?
      | `(tactic| have $_:letPatDecl)
      | `(tactic| have $_ : $_ := $_) =>
        let some initialGoal := getInitialGoal as
          | throw <| IO.userError "initial goal is expected for have"
        return {result with steps :=
                  [.haveDecl tacticApp initialGoal as]}
      | `(tactic| rw [$_,*] $(_)?)
      | `(tactic| rewrite [$_,*] $(_)?) =>
        let prettify (tStr : String) :=
          let res := tStr.trim.dropRightWhile (· == ',')
          -- rw puts final rfl on the "]" token
          if res == "]" then "rfl" else res
        return {result with steps := as.map fun a => 
          match a with
          | .tacticApp a => .tacticApp { a with tacticString := s!"rw [{prettify a.tacticString}]" }
          | x => x}
      | _ =>
        -- Case for `cases` and `induction`.
        let newGoalIds := (res.map (·.goalsBefore)).join.foldl (fun hs g => hs.insert g.id) HashSet.empty
        let mut unmatchedGoalIds := (goalsBefore :: (res.map (·.goalsAfter))).join.foldl (fun hs g => hs.erase g.id) newGoalIds
        let unmatchedGoals := (res.map (·.goalsBefore)).join.filter fun g => unmatchedGoalIds.contains g.id
        if !unmatchedGoals.isEmpty then
          dbg_trace "unmatched goals: {toJson unmatchedGoals}"
          return {result with steps := 
                    .tacticApp {tacticApp with goalsBefore := [goalsBefore[0]!], goalsAfter := unmatchedGoals} :: as}
        return result
    else
      -- TODO: It should propagate goals probably.
      return {goalsBefore := [], goalsAfter := [], steps := as}
  | none, .node .. => panic! "unexpected context-free info tree node"
  | _, .context ctx t => go ctx t
  | _, .hole .. => pure {goalsBefore := [], goalsAfter := [], steps := []}
    