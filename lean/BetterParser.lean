import Lean
import Lean.Meta.Basic
import Lean.Meta.CollectMVars
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
  id : MVarId
  deriving Inhabited, ToJson, FromJson

instance : BEq GoalInfo where
  beq g1 g2 := g1.id == g2.id

instance : Hashable GoalInfo where
  hash g := hash g.id

structure ProofStep where
  tacticString    : String
  goalBefore      : GoalInfo
  goalsAfter      : List GoalInfo
  tacticDependsOn : List String
  spawnedGoals    : List GoalInfo
  deriving Inhabited, ToJson, FromJson

def stepGoalsAfter (step : ProofStep) : List GoalInfo := step.goalsAfter ++ step.spawnedGoals

def noInEdgeGoals (allGoals : Std.HashSet GoalInfo) (steps : List ProofStep) : Std.HashSet GoalInfo :=
  -- Some of the orphaned goals might be matched by tactics in sibling subtrees, e.g. for tacticSeq.
  (steps.bind stepGoalsAfter).foldl Std.HashSet.erase allGoals

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
  let fullExpr ← instantiateExprMVars expr
  let fvarIds := (collectFVars {} fullExpr).fvarIds
  let fvars := fvarIds.filterMap goalDecl.lctx.find?
  let proofFvars ← fvars.filterM (Meta.isProof ·.toExpr)
  -- let pretty := proofFvars.map (fun x => x.userName)
  -- dbg_trace s!"Used {pretty}"
  return proofFvars.map (fun x => x.fvarId.name.toString) |>.toList

-- This is used to match goalsBefore with goalsAfter to see what was assigned to what
def findMVarsAssigned (goalId : MVarId) (mctxAfter : MetavarContext) : MetaM (List MVarId) := do
  let some expr := mctxAfter.eAssignment.find? goalId
    | return []
  let (_, s) ← (Meta.collectMVars expr).run {}
  return s.result.toList

def mayBeProof (expr : Expr) : MetaM String := do
  let type : Expr ← Lean.Meta.inferType expr
  if ← Meta.isProof expr then
    return "proof"
  if type.isSort then
    return "universe"
  else
    return "data"

def printGoalInfo (printCtx : ContextInfo) (id : MVarId) : IO GoalInfo := do
  let some decl := printCtx.mctx.findDecl? id
    | panic! "printGoalInfo: goal not found in the mctx"
  -- to get tombstones in name ✝ for unreachable hypothesis
  let lctx := decl.lctx |>.sanitizeNames.run' {options := {}}
  let ppContext := printCtx.toPPContext lctx
  let hyps ← lctx.foldrM (init := []) (fun hypDecl acc => do
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
    } : Hypothesis) :: acc)
  return ⟨ decl.userName.toString, (← ppExprWithInfos ppContext decl.type).fmt.pretty, hyps, id⟩

-- Returns unassigned goals from the provided list of goals
def getUnassignedGoals (goals : List MVarId) (mctx : MetavarContext) : IO (List MVarId) := do
  goals.filterMapM fun id => do
    if let none := mctx.findDecl? id then
      return none
    if mctx.eAssignment.contains id ||
       mctx.dAssignment.contains id then
      return none
    return some id

structure Result where
  steps : List ProofStep
  allGoals : Std.HashSet GoalInfo

/--
  Transforms `.tacticString`-s of children nodes if their parent is `rw`.

  @EXAMPLES

  "Set.mem_inter_iff," => "rw [Set.mem_inter_iff]"
  "and_comm"           => "rw [and_comm]"
  "]"                  => "rw [rfl]"
-/
def prettifySteps (ts : String) (steps : List ProofStep) : List ProofStep :=
  let prettifyRw (tacticString: String) (steps: List ProofStep) : List ProofStep := steps.map λ step =>
    if step.tacticString.startsWith tacticString then step
    else
      let rwPart := if step.tacticString == "]"
        then "rfl"
        else step.tacticString.trim.dropRightWhile (· == ',')
      { step with tacticString := s!"{tacticString} [{rwPart}]" }
  -- ___Why don't we match by syntax instead?
  --    Many of these tactics are defined Mathlib (ntw_rw, nth_rewrite, rw_mod_cast), and we'd need to import Mathlib to be able to match them by syntax.
  --    We don't want Paperproof to depend on Mathlib however.
  if ts.startsWith "rw "          then prettifyRw "rw"          steps else
  if ts.startsWith "erw "         then prettifyRw "erw"         steps else
  if ts.startsWith "rwa "         then prettifyRw "rwa"         steps else
  if ts.startsWith "rewrite "     then prettifyRw "rewrite"     steps else
  if ts.startsWith "nth_rw "      then prettifyRw "nth_rw"      steps else
  if ts.startsWith "nth_rewrite " then prettifyRw "nth_rewrite" steps else
  if ts.startsWith "rw_mod_cast " then prettifyRw "rw_mod_cast" steps
  else steps

-- Comparator for names, e.g. so that _uniq.34 and _uniq.102 go in the right order.
-- That's not completely right because it doesn't compare prefixes but
-- it's much shorter to write than correct version and serves the purpose.
def nameNumLt (n1 n2 : Name) : Bool :=
  match n1, n2 with
  | .num _ n₁, .num _ n₂ => n₁ < n₂
  | .num _ _,  _ => true
  | _, _ => false

/--
  InfoTree has a lot of non-user-written intermediate `TacticInfo`s, this function returns `none` for those.

  @EXAMPLES

  `tInfo.stx`               //=> `(Tactic.tacticSeq1Indented [(Tactic.exact "exact" (Term.proj ab "." (fieldIdx "2")))])`
  `tInfo.stx.getSubstring?` //=> `(some (exact ab.2 ))`

  `tInfo.stx`               //=> `(Tactic.rotateRight "rotate_right" []) -- (that's not actually present in our proof)`
  `tInfo.stx.getSubstring?` //=> `None`
-/
def getTacticStringUserWrote (tInfo : TacticInfo) : Option String :=
  match tInfo.stx.getSubstring? with
  | .some substring => substring.toString
  | .none => none

/--
  By default, `.getSubstring()` captures empty lines and comments after the tactic - this function removes them.
-/
def prettifyTacticString (tacticString: String) : String :=
  (tacticString.splitOn "\n").head!.trim

def getRelevantGoalsAfter (ctx : ContextInfo) (goalBeforeDecl: MetavarDecl) (mctxAfter: MetavarContext) (goalBeforeId: MVarId) (goalsAfter: List MVarId) : IO (List MVarId) := do
  ContextInfo.runMetaM ctx goalBeforeDecl.lctx do
    let assignedToThisGoal := match mctxAfter.eAssignment.find? goalBeforeId with
      | some expr => do return (← Meta.getMVars expr).toList
      | none      => do return []
    let wow ← assignedToThisGoal
    return goalsAfter.filter (λ g => wow.contains g)


partial def postNode (ctx : ContextInfo) (info : Info) (_: PersistentArray InfoTree) (results : List (Option Result)) : IO Result := do
  -- Remove `Option.none` values from the `results` list (we have them because of the `.visitM` implementation)
  let results : List Result := results.filterMap id
  -- 1. Flatten `ProofStep`s
  let steps : List ProofStep := (results.map (λ result => result.steps)).join
  -- 2. Flatten `GoalInfo`s
  let allGoals := Std.HashSet.empty.insertMany ((results.map (λ result => result.allGoals.toList)).join)

  let .some ctx := info.updateContext? ctx                            | panic! "unexpected context node"
  let .ofTacticInfo tInfo := info                                     | return { steps, allGoals }
  let .some userWrittenTacticString := getTacticStringUserWrote tInfo | return { steps, allGoals }

  let tacticString := prettifyTacticString userWrittenTacticString

  let steps := prettifySteps userWrittenTacticString steps

  -- For printing purposes we always need to use the latest mctx assignments. For example in
  -- have h := by calc
  --  3 ≤ 4 := by trivial
  --  4 ≤ 5 := by trivial
  -- at mctxBefore type of `h` is `?m.260`, but by the time calc is elaborated at mctxAfter
  -- it's known to be `3 ≤ 5`
  let printCtx := { ctx with mctx := tInfo.mctxAfter }

  let goalsThatDisappeared := tInfo.goalsBefore.filter λ goalBefore =>
    !tInfo.goalsAfter.contains goalBefore &&
    -- Leave only steps which are not handled in the subtree.
    !(steps.map (λ step => step.goalBefore.id)).contains goalBefore

  -- We need to match them into (goalBefore, goalsAfter) pairs according to assignment.
  let mut newSteps : List ProofStep := []
  -- Typically we only work on one goal, so only one proofStep gets added!
  for goalBefore in goalsThatDisappeared do
    if let some goalDecl := tInfo.mctxBefore.findDecl? goalBefore then
    
      let relevantGoalsAfter ← getRelevantGoalsAfter ctx goalDecl tInfo.mctxAfter goalBefore tInfo.goalsAfter
      newSteps := {
        tacticString,
        goalBefore      := ← printGoalInfo printCtx goalBefore,
        goalsAfter      := ← relevantGoalsAfter.mapM (printGoalInfo printCtx),
        tacticDependsOn := ← ContextInfo.runMetaM ctx goalDecl.lctx (findHypsUsedByTactic goalBefore goalDecl tInfo.mctxAfter)
        spawnedGoals    := []
      } :: newSteps

  let currentGoals := (newSteps.map (λ step => step.goalBefore :: step.goalsAfter)).join
  let allGoals := allGoals.insertMany currentGoals
  -- It's like tacticDependsOn but unnamed mvars instead of hyps.
  -- Important to sort for have := calc for example, e.g. calc 3 < 4 ... 4 < 5 ...
  let orphanedGoals := currentGoals.foldl Std.HashSet.erase (noInEdgeGoals allGoals steps)
    |>.toArray.insertionSort (nameNumLt ·.id.name ·.id.name) |>.toList
  
  newSteps := newSteps.map λ s => { s with spawnedGoals := orphanedGoals }

  return { steps := newSteps ++ steps, allGoals }


partial def BetterParser (i : InfoTree) := i.visitM (postNode := postNode)
