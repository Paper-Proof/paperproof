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

instance : BEq GoalInfo where
  beq g1 g2 := g1.id == g2.id

instance : Hashable GoalInfo where
  hash g := hash g.id

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

def stepGoalsAfter (step : ProofStep) : List GoalInfo := match step with
  | .tacticApp t => t.goalsAfter
  | .haveDecl t _ _ => t.goalsAfter

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
    let ppContext := {ctx with mctx}.toPPContext lctx
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

structure Result where
  steps : List ProofStep
  orphanedGoals : List GoalInfo

partial def parse (infoTree : InfoTree) : IO Proof := do
  let result ← (go none infoTree : IO Result)
  let some statement := result.orphanedGoals.head?.map (·.type)
    | throw <| IO.userError "initial goal is expected for theorem"
  return {statement, steps := result.steps}
where go
  | some (ctx : ContextInfo), .node i cs => do
    let newCtx := i.updateContext? ctx
    let res ← cs.toList.mapM (go newCtx)
    let steps := res.map (fun r => r.steps) |>.join
    let mut orphanedGoals := HashSet.empty.insertMany $ res.bind (·.orphanedGoals)
    -- Some of the orphaned goals might be matched by tactics in sibling subtrees, e.g. for tacticSeq.
    orphanedGoals := steps.bind stepGoalsAfter |>.foldl HashSet.erase orphanedGoals
    if let .ofTacticInfo tInfo := i then
      let goalsBefore ← getGoals ctx tInfo.goalsBefore tInfo.mctxBefore
      let goalsAfter ← getGoals ctx tInfo.goalsAfter tInfo.mctxAfter
      -- Tactic doesn't change any goals, we shouldn't add it as a proof step.
      if goalsBefore == goalsAfter then
        return {steps, orphanedGoals := orphanedGoals.toList}
      -- shortcut if it's not a tactic user wrote
      -- \n trim to avoid empty lines/comments until next tactic,
      -- especially at the end of theorem it will capture comment for the next one
      let some tacticString := tInfo.stx.getSubstring?.map
             (·.toString |>.splitOn "\n" |>.head!.trim)
      -- otherwise it's a synthetic tactic and we can't attach any proof steps to it
        | return {steps, orphanedGoals := goalsBefore ++ orphanedGoals.toList}
      let some mainGoalDecl := tInfo.goalsBefore.head?.bind tInfo.mctxBefore.findDecl?
        -- For example a tactic like `done` just ensures there are no unsolved goals,
        -- however has no information for the tactic tree
        | return {steps, orphanedGoals := orphanedGoals.toList}
      
      -- Find names to get decls
      let fvarIds := cs.toList.map (findFVars ctx) |>.join
      let fvars := fvarIds.filterMap mainGoalDecl.lctx.find?
      let tacticApp: TacticApplication := {
          tacticString,
          goalsBefore,
          goalsAfter,
          tacticDependsOn := fvars.map fun decl => s!"{decl.fvarId.name.toString}"
          }
      if steps.isEmpty then
        -- When `childrenProfoSteps` is non-empty it's a tactic combinator, i.e. there are more granular tactics
        -- in the subtree. For example `have` with `by` or `rw [a,b]`
        -- Otherwise it's a tactic like `apply`, `exact`, `simp`, or a simple `have` defined in term mode etc.
        return {steps := [.tacticApp tacticApp], orphanedGoals := goalsBefore} 
      
      -- It's a tactic combinator
      match tInfo.stx with
      -- TODO: can we grab all have's as one pattern match branch?
      | `(tactic| have $_:letPatDecl)
      | `(tactic| have $_ : $_ := $_) =>
        -- TODO: Goals after shouldn't be needed because some edge from 1 -> 1 is getting it
        orphanedGoals := (goalsBefore).foldl HashSet.erase orphanedGoals
        let [initialGoal] := orphanedGoals.toList
          -- TODO: have ⟨ p, q ⟩ : (a = a) × (b = b) := ⟨ by rfl, by rfl ⟩ isn't supported yet
          | throw <| IO.userError s!"exactly one orphaned goal is expected for have, but found {toJson orphanedGoals.toList}"
        return {steps := [.haveDecl tacticApp initialGoal.type steps], orphanedGoals := goalsBefore}
      | `(tactic| rw [$_,*] $(_)?)
      | `(tactic| rewrite [$_,*] $(_)?) =>
        let prettify (tStr : String) :=
          let res := tStr.trim.dropRightWhile (· == ',')
          -- rw puts final rfl on the "]" token
          if res == "]" then "rfl" else res
        return {steps := steps.map fun a => 
                  match a with
                  | .tacticApp a => .tacticApp { a with tacticString := s!"rw [{prettify a.tacticString}]" }
                  | x => x,
                orphanedGoals := goalsBefore}
      | _ =>
        -- Case for `cases` and `induction`.
        let mainGoal := goalsBefore.head!
        orphanedGoals := orphanedGoals.erase mainGoal
        if !orphanedGoals.isEmpty then
          -- TODO: Maybe it should be returning a tacticApp?
          return {
            steps := .tacticApp {tacticApp with goalsBefore := [mainGoal], goalsAfter := orphanedGoals.toList} :: steps,
            orphanedGoals := goalsBefore}
        else
          return {steps, orphanedGoals := goalsBefore} 
    else
      return { steps, orphanedGoals := orphanedGoals.toList}
  | none, .node .. => panic! "unexpected context-free info tree node"
  | _, .context ctx t => go ctx t
  | _, .hole .. => pure {steps := [], orphanedGoals := []}
    