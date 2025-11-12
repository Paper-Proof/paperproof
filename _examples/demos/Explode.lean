import Mathlib.Tactic.Cases
import Mathlib.Tactic.Explode
import Paperproof

elab "myPersonalTactic" : tactic => do
  let mvarId ← Lean.Elab.Tactic.getMainGoal
  let term ← `(λ a b ab => And.casesOn (motive := λ t => ab = t → b ∧ a) ab (λ hA hB _ => And.intro hB hA) (Eq.refl ab))
  let expr ← Lean.Elab.Tactic.elabTerm term none
  mvarId.assign expr

theorem tacticProof (a b : Prop) : a ∧ b → b ∧ a := by
  intro ab
  rcases ab with ⟨hA, hB⟩
  apply And.intro
  exact hB
  exact hA

theorem prooftermProof (a b : Prop) : a ∧ b → b ∧ a :=
  λ ab => And.casesOn (motive := λ t => ab = t → b ∧ a) ab (λ hA hB _ => And.intro hB hA) (Eq.refl ab)

theorem sweepingTacticProof : ∀ (a b : Prop), a ∧ b → b ∧ a := by
  myPersonalTactic

-- #explode results in exactly the same output, because it's based on `Expr`s.
-- Contrast this with Paperproof outputs, which are based on `InfoTree`s.
#explode tacticProof
#explode prooftermProof
#explode sweepingTacticProof
