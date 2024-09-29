import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.List.Chain
import Mathlib.Tactic.Linarith
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Algebra.GCDMonoid.Multiset
import Lean
import Paperproof

open Lean Lean.Elab

--------- NATURAL DEDUCTION: basic building blocks ---------
variable (OurGoal: Prop)

-- CONJUNCTION
theorem andIntroductionTop {A B : Prop} (h1 : A) (h2 : B) : OurGoal := by
  have h := And.intro h1 h2
  all_goals sorry
theorem andIntroductionBottom {A B : Prop} (h1 : A) (h2 : B) : A ∧ B := by
  apply And.intro
  all_goals sorry
theorem andEliminationTop {A B : Prop} (h : A ∧ B) : OurGoal := by
  -- have h1 := h.left
  apply And.left at h
  sorry
theorem andEliminationBottom {A B : Prop} : A := by
  apply And.left (a := A) (b := B)
  sorry

-- DISJUNCTION
theorem orIntroductionTop {A B : Prop} (h : A) : OurGoal := by
  have ab : A ∨ B := Or.inl h
  sorry
theorem orIntroductionBottom {A B : Prop} : A ∨ B := by
  apply Or.inl
  sorry
theorem orEliminationTop {A B : Prop} (h : A ∨ B) : OurGoal := by
  cases' h with a b
  all_goals sorry
theorem orEliminationBottom {A B : Prop} : OurGoal := by
  apply Or.elim (a := A) (b := B)
  all_goals sorry

-- IMPLICATION
theorem arrowIntroductionTop {A B : Prop} (b : B) : OurGoal := by
  let h := λ a : A => b
  sorry
theorem arrowIntroductionBottom {A B : Prop} : A → B := by
  intro a
  sorry
theorem arrowEliminationTop {A B : Prop} (a : A) (ab : A → B) : OurGoal := by
  let h := ab a
  sorry
theorem arrowEliminationBottom {A B : Prop} (a : A) : B := by
  revert a
  sorry

-- THE UNIVERSAL QUANTIFIER
theorem forallIntroductionBottom {α : Type} {A : α → Prop} : ∀ y, A y := by
  intro x
  sorry
theorem forallEliminationTop {α : Type} {A : α → Prop}
  (h : ∀ x, A x) (t : α) : OurGoal := by
  let s := h t
  sorry
-- Corresponding Top & Bottom rules are hard to achieve with tactics, there are no tactics for turning free vars into foralls afaik

-- THE EXISTENTIAL QUANTIFIER
theorem existsIntroductionTop {α : Type} {A : α → Prop} {t: α} (h : A t) : OurGoal := by
  have h2 : ∃ x, A x := Exists.intro t h
  sorry
theorem existsIntroductionBottom {α : Type} {A : α → Prop} {t: α} : ∃ x, A x := by
  apply Exists.intro (w := t)
  sorry
theorem existsEliminationTop {α : Type} {A : α → Prop} (h : ∃ x, A x) : OurGoal := by
  cases' h with y h1
  sorry
theorem existsEliminationBottom {α : Type} {A : α → Prop} (h : ∃ x, A x) (t : α) : A t := by
  apply Exists.elim (p := A)
  all_goals sorry
-- WILD versions are veridical reproduction of what we see in logic textbooks. In lean we'll be using normal versions though.
theorem existsEliminationTopWILD {α : Type} {B : Prop} {A : α → Prop} (h : ∃ x, A x) (hi : ∀ y, A y → B) : OurGoal := by
  cases' h with s h2
  let h3 := hi s h2
  sorry
theorem existsEliminationBottomWILD {α : Type} {A : α → Prop} {B: Prop} : B := by
  apply Exists.elim (p := A)
  sorry
  intro y
  sorry

--------- NATURAL DEDUCTION: full-fledged theorems ---------

-- The natural deduction trees accompanying these proofs can be seen in "Logic and Proof" (Jeremy Avigad, Robert Y. Lewis, Floris van Doorn) textbook.

-- We can interpret the natural deduction tree as either page66_evenOdd_TOP or page66_evenOdd_BOTTOM
theorem page66_evenOdd_TOP {even : ℕ → Prop} {odd : ℕ → Prop} (h1: ∀n, (¬ even n → odd n)) : ∀ n, (even n) ∨ (odd n) := by
  intro x
  have h := Classical.em (even x)
  cases' h with hi hello
  left
  exact hi
  right
  exact h1 x hello

theorem page66_evenOdd_BOTTOM {even : ℕ → Prop} {odd : ℕ → Prop} (h1: ∀n, (¬ even n → odd n)) : ∀ n, (even n) ∨ (odd n) := by
  intro x
  have h := Classical.em
  apply Or.elim (a := even x) (b := ¬ even x)
  apply h
  intro hi
  left
  exact hi
  intro hello
  right
  exact h1 x hello
