import Lean
import Lean.Meta.Basic
open Lean Elab Server

structure Hypothesis where
  username : String
  type : String
  value : Option String
  -- unique identifier for the hypothesis, fvarId
  id : String
  isProof : String
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
  | .haveDecl t initialGoals _ => t.goalsAfter ++ initialGoals

def stepGoalsBefore (step : ProofStep) : List GoalInfo := match step with
  | .tacticApp t => t.goalsBefore
  | .haveDecl t _ _ => t.goalsBefore

def noInEdgeGoals (allGoals : HashSet GoalInfo) (steps : List ProofStep) : HashSet GoalInfo :=
  -- Some of the orphaned goals might be matched by tactics in sibling subtrees, e.g. for tacticSeq.
  (steps.bind stepGoalsAfter).foldl HashSet.erase allGoals

/-
  Instead of doing parsing of what user wrote (it wouldn't work for linarith etc),
  let's do the following.
  We have assigned something to our goal in mctxAfter.
  All the fvars used in these assignments are what was actually used instead of what was in syntax.
-/
def findHypsUsedByTactic (goalId: MVarId) (goalDecl : MetavarDecl) (mctxAfter : MetavarContext) : MetaM (List String) := do
  let some expr := mctxAfter.eAssignment.find? goalId
    | return []

  -- Need to instantiate it to get all fvars
  let fullExpr ← instantiateExprMVars expr |>.run
  let fvarIds := (collectFVars {} fullExpr).fvarIds
  let fvars := fvarIds.filterMap goalDecl.lctx.find?
  let proofFvars ← fvars.filterM (Meta.isProof ·.toExpr)
  -- let pretty := proofFvars.map (fun x => x.userName)
  -- dbg_trace s!"Used {pretty}"
  return proofFvars.map (fun x => x.fvarId.name.toString) |>.toList

def mayBeProof (expr : Expr) : MetaM String := do
  let type : Expr ← Lean.Meta.inferType expr
  if ← Meta.isProof expr then
    return "proof"
  if type.isSort then
    return "universe"
  else
    return "data"

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
    let hyps ← lctx.foldlM (init := []) (fun acc hypDecl => do
      if hypDecl.isAuxDecl || hypDecl.isImplementationDetail then
        return acc
      let type ← liftM (ppExprWithInfos ppContext hypDecl.type)
      let value ← liftM (hypDecl.value?.mapM (ppExprWithInfos ppContext))
      let isProof : String ← printCtx.runMetaM decl.lctx (mayBeProof hypDecl.toExpr)
      return ({
        username := hypDecl.userName.toString,
        type := type.fmt.pretty,
        value := value.map (·.fmt.pretty),
        id := hypDecl.fvarId.name.toString,
        isProof := isProof
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

      let some mainGoalId := tInfo.goalsBefore.head?
        | return {steps, allGoals}
      let some mainGoalDecl := tInfo.mctxBefore.findDecl? mainGoalId
        | return {steps, allGoals}

      let tacticDependsOn ←
        ctx.runMetaM mainGoalDecl.lctx
          (findHypsUsedByTactic mainGoalId mainGoalDecl tInfo.mctxAfter)
      let tacticApp: TacticApplication := {
        tacticString,
        goalsBefore,
        goalsAfter,
        tacticDependsOn
      }
      -- It's like tacticDependsOn but unnamed mvars instead of hyps.
      let orphanedGoals := (goalsBefore ++ goalsAfter).foldl HashSet.erase (noInEdgeGoals allGoals steps)

      -- It's a tactic combinator
      match tInfo.stx with
      | `(tactic| have $_:haveDecl) =>
        -- Something like `have p : a = a := rfl`
        if steps.isEmpty then
          return {steps := [.tacticApp tacticApp],
                  allGoals}

        -- Important for have := calc for example, e.g. calc 3 < 4 ... 4 < 5 ...
        let sortedGoals := orphanedGoals.toArray.insertionSort (·.id < ·.id)
        return {steps := [.haveDecl tacticApp sortedGoals.toList []] ++ steps,
                allGoals}
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
        return {steps := .tacticApp {tacticApp with goalsAfter := goalsAfter ++ orphanedGoals.toList} :: steps,
                allGoals}
    else
      return { steps, allGoals := allSubGoals}
  | none, .node .. => panic! "unexpected context-free info tree node"
  | _, .context ctx t => BetterParser ctx t
  | _, .hole .. => pure {steps := [], allGoals := .empty}
