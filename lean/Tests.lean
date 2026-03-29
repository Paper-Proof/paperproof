import Lean
import Lean.Elab.Command
import Services.BetterParser
import Mathlib.Data.Set.Basic
import Paperproof

open Lean Elab Command 

private def formatGoalInfo (indent : String) (g : Paperproof.Services.GoalInfo) : String :=
  let hyps :=
    if g.hyps.isEmpty then s!"{indent}  hyps: (none)"
    else s!"{indent}  hyps:\n" ++ String.intercalate "\n" (g.hyps.map fun h => s!"{indent}    {h.username} : {h.type}")
  s!"{indent}  type: {g.type}\n{hyps}"

private def formatGoalList (label : String) (goals : List Paperproof.Services.GoalInfo) : String :=
  if goals.isEmpty then s!"{label}: (none)"
  else s!"{label}:\n" ++ String.intercalate "\n  ============================\n" (goals.map (formatGoalInfo ""))

private def formatDependsOn (ids : List String) (hyps : List Paperproof.Services.Hypothesis) : String :=
  let names := ids.filterMap fun id => hyps.find? (·.id == id) |>.map (·.username)
  if names.isEmpty then "dependsOn: (none)" else s!"dependsOn: {String.intercalate ", " names}"

private def formatResult (r : Paperproof.Services.Result) : String :=
  String.intercalate "\n\n" <| r.steps.zipIdx.map fun (step, i) =>
    let goalBefore := s!"goalBefore:\n{formatGoalInfo "" step.goalBefore}"
    let goalsAfter := formatGoalList "goalsAfter"   step.goalsAfter
    let spawned    := formatGoalList "spawnedGoals" step.spawnedGoals
    let depOn      := formatDependsOn step.tacticDependsOn step.goalBefore.hyps
    s!"[step {i + 1}]\ntactic: {step.tacticString}\n{goalBefore}\n{goalsAfter}\n{spawned}\n{depOn}"

syntax (name := assertParserCmd) "#assert_parser" "in" command : command
@[command_elab assertParserCmd]
def elabAssertParser : CommandElab
  | `(command| #assert_parser in $cmd) => do
    let fileMap ← getFileMap
    elabCommand cmd
    for tree in (← getInfoState).substituteLazy.get.trees do
      let some r ← liftTermElabM (liftM (Paperproof.Services.BetterParser_Tree fileMap tree)) | continue
      if !r.steps.isEmpty then logInfo (formatResult r)
  | _ => throwUnsupportedSyntax

-- =============================================================================
-- Tests
-- =============================================================================

/--
info: [step 1]
tactic: exact Nat.add_comm a b
goalBefore:
  type: a + b = b + a
  hyps:
    a : ℕ
    b : ℕ
goalsAfter: (none)
spawnedGoals: (none)
dependsOn: a, b
-/
#guard_msgs in
#assert_parser in
theorem simple (a b : ℕ) : a + b = b + a := by
  exact Nat.add_comm a b

/--
info: [step 1]
tactic: ext x
goalBefore:
  type: s ∩ t = t ∩ s
  hyps:
    s : Set ℕ
    t : Set ℕ
goalsAfter:
  type: x ∈ s ∩ t ↔ x ∈ t ∩ s
  hyps:
    s : Set ℕ
    t : Set ℕ
    x : ℕ
spawnedGoals: (none)
dependsOn: s, t

[step 2]
tactic: apply Iff.intro
goalBefore:
  type: x ∈ s ∩ t ↔ x ∈ t ∩ s
  hyps:
    s : Set ℕ
    t : Set ℕ
    x : ℕ
goalsAfter:
  type: x ∈ s ∩ t → x ∈ t ∩ s
  hyps:
    s : Set ℕ
    t : Set ℕ
    x : ℕ
  ============================
  type: x ∈ t ∩ s → x ∈ s ∩ t
  hyps:
    s : Set ℕ
    t : Set ℕ
    x : ℕ
spawnedGoals: (none)
dependsOn: s, t, x

[step 3]
tactic: intro h1
goalBefore:
  type: x ∈ s ∩ t → x ∈ t ∩ s
  hyps:
    s : Set ℕ
    t : Set ℕ
    x : ℕ
goalsAfter:
  type: x ∈ t ∩ s
  hyps:
    s : Set ℕ
    t : Set ℕ
    x : ℕ
    h1 : x ∈ s ∩ t
spawnedGoals: (none)
dependsOn: s, t, x

[step 4]
tactic: rw [Set.mem_inter_iff]
goalBefore:
  type: x ∈ t ∩ s
  hyps:
    s : Set ℕ
    t : Set ℕ
    x : ℕ
    h1 : x ∈ s ∩ t
goalsAfter:
  type: x ∈ t ∩ s
  hyps:
    s : Set ℕ
    t : Set ℕ
    x : ℕ
    h1 : x ∈ s ∧ x ∈ t
spawnedGoals: (none)
dependsOn: s, t, x, h1

[step 5]
tactic: rw [and_comm]
goalBefore:
  type: x ∈ t ∩ s
  hyps:
    s : Set ℕ
    t : Set ℕ
    x : ℕ
    h1 : x ∈ s ∧ x ∈ t
goalsAfter:
  type: x ∈ t ∩ s
  hyps:
    s : Set ℕ
    t : Set ℕ
    x : ℕ
    h1 : x ∈ t ∧ x ∈ s
spawnedGoals: (none)
dependsOn: s, x, t, h1

[step 6]
tactic: exact h1
goalBefore:
  type: x ∈ t ∩ s
  hyps:
    s : Set ℕ
    t : Set ℕ
    x : ℕ
    h1 : x ∈ t ∧ x ∈ s
goalsAfter: (none)
spawnedGoals: (none)
dependsOn: h1

[step 7]
tactic: intro h2
goalBefore:
  type: x ∈ t ∩ s → x ∈ s ∩ t
  hyps:
    s : Set ℕ
    t : Set ℕ
    x : ℕ
goalsAfter:
  type: x ∈ s ∩ t
  hyps:
    s : Set ℕ
    t : Set ℕ
    x : ℕ
    h2 : x ∈ t ∩ s
spawnedGoals: (none)
dependsOn: t, s, x

[step 8]
tactic: rw [Set.mem_inter_iff]
goalBefore:
  type: x ∈ s ∩ t
  hyps:
    s : Set ℕ
    t : Set ℕ
    x : ℕ
    h2 : x ∈ t ∩ s
goalsAfter:
  type: x ∈ s ∩ t
  hyps:
    s : Set ℕ
    t : Set ℕ
    x : ℕ
    h2 : x ∈ t ∧ x ∈ s
spawnedGoals: (none)
dependsOn: t, s, x, h2

[step 9]
tactic: rw [and_comm]
goalBefore:
  type: x ∈ s ∩ t
  hyps:
    s : Set ℕ
    t : Set ℕ
    x : ℕ
    h2 : x ∈ t ∧ x ∈ s
goalsAfter:
  type: x ∈ s ∩ t
  hyps:
    s : Set ℕ
    t : Set ℕ
    x : ℕ
    h2 : x ∈ s ∧ x ∈ t
spawnedGoals: (none)
dependsOn: t, x, s, h2

[step 10]
tactic: exact h2
goalBefore:
  type: x ∈ s ∩ t
  hyps:
    s : Set ℕ
    t : Set ℕ
    x : ℕ
    h2 : x ∈ s ∧ x ∈ t
goalsAfter: (none)
spawnedGoals: (none)
dependsOn: h2
-/
#guard_msgs in
#assert_parser in
theorem commutativityOfIntersections (s t : Set ℕ) : s ∩ t = t ∩ s := by
  ext x
  apply Iff.intro

  intro h1
  rw [Set.mem_inter_iff, and_comm] at h1
  exact h1

  intro h2
  rw [Set.mem_inter_iff, and_comm] at h2
  exact h2

/--
info: [step 1]
tactic: have easy: 4 = 2 + 2 := by rfl
goalBefore:
  type: 666 = 665 + 1
  hyps: (none)
goalsAfter:
  type: 666 = 665 + 1
  hyps:
    easy : 4 = 2 + 2
spawnedGoals:
  type: 4 = 2 + 2
  hyps: (none)
dependsOn: (none)

[step 2]
tactic: rfl
goalBefore:
  type: 4 = 2 + 2
  hyps: (none)
goalsAfter: (none)
spawnedGoals: (none)
dependsOn: (none)

[step 3]
tactic: simp
goalBefore:
  type: 666 = 665 + 1
  hyps:
    easy : 4 = 2 + 2
goalsAfter: (none)
spawnedGoals: (none)
dependsOn: (none)
-/
#guard_msgs in
#assert_parser in
theorem spawned : 666 = 665 + 1 := by
  have easy: 4 = 2 + 2 := by rfl
  simp
