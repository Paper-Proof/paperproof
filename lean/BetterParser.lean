import Lean
import Lean.Meta.Basic
open Lean Elab Server

structure Hypothesis where
  username : String
  type : String
  value : Option String
  -- unique identifier for the hypothesis, fvarId
  id : String
  deriving Inhabited, ToJson, FromJson

structure GoalInfo where
  username : String
  type : String
  hyps : List Hypothesis 
  -- unique identifier for the goal, mvarId
  id : String
  deriving Inhabited, ToJson, FromJson

instance : BEq GoalInfo where
  beq g1 g2 := g1.id == g2.id

instance : Hashable GoalInfo where
  hash g := hash g.id

structure TacticApplication where
  tacticString : String
  goalsBefore : List GoalInfo
  goalsAfter : List GoalInfo 
  tacticDependsOn : List String
  deriving Inhabited, ToJson, FromJson

inductive ProofStep := 
  | tacticApp (t : TacticApplication)
  | haveDecl (t: TacticApplication)
    (initialGoals: List GoalInfo)
    (subSteps : List ProofStep)
  deriving Inhabited, ToJson, FromJson

def stepGoalsAfter (step : ProofStep) : List GoalInfo := match step with
  | .tacticApp t => t.goalsAfter
  | .haveDecl t _ _ => t.goalsAfter

def stepGoalsBefore (step : ProofStep) : List GoalInfo := match step with
  | .tacticApp t => t.goalsBefore
  | .haveDecl t _ _ => t.goalsBefore

def noInEdgeGoals (allGoals : HashSet GoalInfo) (steps : List ProofStep) : HashSet GoalInfo :=
  -- Some of the orphaned goals might be matched by tactics in sibling subtrees, e.g. for tacticSeq.
  (steps.bind stepGoalsAfter).foldl HashSet.erase allGoals

partial def findFVars (ctx: ContextInfo) (infoTree : InfoTree): List FVarId :=
  (InfoTree.context ctx infoTree).deepestNodes fun _ i _ =>
    match i with
    | .ofTermInfo ti  => if let .fvar id := ti.expr then some id else none
    | _ => none 

-- Returns GoalInfo about unassigned goals from the provided list of goals
def getGoals (printCtx: ContextInfo) (goals : List MVarId) (mctx : MetavarContext) : RequestM (List GoalInfo) := do
  goals.filterMapM fun id => do
    let some decl := mctx.findDecl? id
      | return none
    if mctx.eAssignment.contains id ||
       mctx.dAssignment.contains id then
      return none
    -- to get tombstones in name ✝ for unreachable hypothesis
    let lctx := decl.lctx |>.sanitizeNames.run' {options := {}}
    let ppContext := printCtx.toPPContext lctx
    let hyps ← lctx.foldlM (init := []) (fun acc decl => do
      if decl.isAuxDecl || decl.isImplementationDetail then
        return acc
      let type ← liftM (ppExprWithInfos ppContext decl.type)
      let value ← liftM (decl.value?.mapM (ppExprWithInfos ppContext))
      return ({
        username := decl.userName.toString,
        type := type.fmt.pretty,
        value := value.map (·.fmt.pretty), 
        id := decl.fvarId.name.toString
        } : Hypothesis) ::acc)
    return some ⟨ decl.userName.toString, (← ppExprWithInfos ppContext decl.type).fmt.pretty, hyps, id.name.toString ⟩

structure Result where
  steps : List ProofStep
  allGoals : HashSet GoalInfo

def getGoalsChange (ctx : ContextInfo) (tInfo : TacticInfo) : RequestM (List GoalInfo × List GoalInfo) := do
  -- We want to filter out `focus` like tactics which don't do any assignments
  -- therefore we check all goals on whether they were assigned during the tactic
  let goalMVars := tInfo.goalsBefore ++ tInfo.goalsAfter
  -- For printing purposes we always need to use the latest mctx assignments. For example in
  -- have h := by calc
  --  3 ≤ 4 := by trivial
  --  4 ≤ 5 := by trivial
  -- at mctxBefore type of `h` is `?m.260`, but by the time calc is elaborated at mctxAfter
  -- it's known to be `3 ≤ 5`
  let printCtx := {ctx with mctx := tInfo.mctxAfter}
  let goalsBefore ← getGoals printCtx goalMVars tInfo.mctxBefore
  let goalsAfter ← getGoals printCtx goalMVars tInfo.mctxAfter
  let commonGoals := goalsBefore.filter fun g => goalsAfter.contains g
  return ⟨ goalsBefore.filter (!commonGoals.contains ·), goalsAfter.filter (!commonGoals.contains ·) ⟩

partial def BetterParser (context: Option ContextInfo) (infoTree : InfoTree) : RequestM Result :=
  match context, infoTree with
  | some (ctx : ContextInfo), .node i cs => do
    let some ctx := i.updateContext? ctx
      | panic! "unexpected context node"
    let res ← cs.toList.mapM (BetterParser ctx)
    let steps := res.map (fun r => r.steps) |>.join
    let allSubGoals := HashSet.empty.insertMany $ res.bind (·.allGoals.toList)
    if let .ofTacticInfo tInfo := i then
      -- shortcut if it's not a tactic user wrote
      -- \n trim to avoid empty lines/comments until next tactic,
      -- especially at the end of theorem it will capture comment for the next one
      let some tacticString := tInfo.stx.getSubstring?.map
             (·.toString |>.splitOn "\n" |>.head!.trim)
        | return {steps, allGoals := allSubGoals}

      let (goalsBefore, goalsAfter) ← getGoalsChange ctx tInfo
      let allGoals := allSubGoals.insertMany $ goalsBefore ++ goalsAfter
      -- Tactic doesn't change any goals, we shouldn't add it as a proof step.
      -- For example a tactic like `done` which ensures there are no unsolved goals,
      -- or `focus` which only leaves one goal, however has no information for the tactic tree
      -- Note: tactic like `have` changes the goal as it adds something to the context
      if goalsBefore.isEmpty then
        return {steps, allGoals}

      let some mainGoalDecl := tInfo.goalsBefore.head?.bind tInfo.mctxBefore.findDecl?
        | return {steps, allGoals}
      
      -- Find names to get decls
      let fvarIds := cs.toList.map (findFVars ctx) |>.join
      let fvars := fvarIds.filterMap mainGoalDecl.lctx.find?
      let proofFvars ← fvars.filterM (λ decl => ctx.runMetaM mainGoalDecl.lctx (Meta.isProof decl.toExpr))
      let tacticApp: TacticApplication := {
        tacticString,
        goalsBefore,
        goalsAfter,
        tacticDependsOn := proofFvars.map fun decl => s!"{decl.fvarId.name.toString}"
      }

      -- It's a tactic combinator
      match tInfo.stx with
      | `(tactic| have $_:haveDecl) =>
        -- Something like `have p : a = a := rfl`
        if steps.isEmpty then
          return {steps := [.tacticApp tacticApp],
                  allGoals} 
 
        let goals := (goalsBefore ++ goalsAfter).foldl HashSet.erase (noInEdgeGoals allGoals steps)
        -- TODO: have ⟨ p, q ⟩ : (3 = 3) ∧ (4 = 4) := ⟨ by rfl, by rfl ⟩ isn't supported yet
        return {steps := [.haveDecl tacticApp goals.toList steps],
                allGoals := HashSet.empty.insertMany (goalsBefore ++ goalsAfter)}
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
                allGoals}
      | _ =>
        -- Don't add anything new if we already handled it in subtree.
        if steps.map stepGoalsBefore |>.elem goalsBefore then
          return {steps, allGoals}
        -- It uses allSubGoals instead of allGoals to make tactics like `.` which focus [1, 2, 3] -> [1] goals work.
        -- TODO: Maybe we should just ignore tactics which goalsAfter is a subset of goalsBefore?
        -- But we will need to find a way to understand if tactic actually closed the goal, like `exact ...` and [1, 2] -> [2],
        -- or just focused it `.` and [1, 2] -> [1].
        let orphanedGoals := goalsBefore.foldl HashSet.erase (noInEdgeGoals allSubGoals steps)
        return {steps := .tacticApp {tacticApp with goalsAfter := goalsAfter ++ orphanedGoals.toList} :: steps,
                allGoals}
    else
      return { steps, allGoals := allSubGoals}
  | none, .node .. => panic! "unexpected context-free info tree node"
  | _, .context ctx t => BetterParser ctx t
  | _, .hole .. => pure {steps := [], allGoals := .empty}
