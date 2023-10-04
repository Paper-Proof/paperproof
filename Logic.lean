import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Parity
import Mathlib.Data.List.Chain
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith
import Std.Data.Int.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Algebra.GCDMonoid.Multiset
import Lean
import Paperproof

open Lean Lean.Elab


-- IMPLICATION
-- →I
theorem arrowIntroduction {A B : Prop} : A → B := by
  intro a
  sorry
-- →E
theorem arrowElimination {A B : Prop} (a : A) (ab : A → B) : B := by
  exact ab a

-- THE UNIVERSAL QUANTIFIER
-- These are just lambda abstraction and lambda application.
-- Note how in logic textbooks they miss the `x: α` hypothesis, making it unclear what happenes exactly.
-- "In the introduction rule, 𝑥 should not be free in any uncanceled hypothesis". just means that scopes shouldn't clash.
-- ∀I
theorem forallIntroduction {α : Type} {A : α → Prop} : ∀ y, A y := by
  intro x
  sorry
-- Same here - where did this `t` come from? It was there, it's a part of the proof! 
-- ∀E
theorem forallElimination {α : Type} {A : α → Prop}
  (h : ∀ x, A x) (t : α) : A t := by
  apply h t

-- THE EXISTENTIAL QUANTIFIER
-- Again - textbook's version conceals `t: α` (displayed as the `α` goal)

-- ∃I
theorem existsIntroductionTop {α : Type} {A : α → Prop} {t: α} (h : A t) : True := by
  have mmm : ∃ x, A x := Exists.intro t h
  sorry
theorem existsIntroductionBottom {α : Type} {A : α → Prop} {t: α} : ∃ x, A x := by
  apply Exists.intro (w := t )
  -- change A t
  sorry
  -- sorry
-- TODO induction principle too
-- take some parallel type & split it
-- TODO green arrows
-- ∃E
theorem existsElimination {α : Type} {A : α → Prop} {B: Prop} (h : ∃ x, A x) : B := by
  cases' h with y mmm
  sorry

-- CONJUNCTION
theorem andIntroductionTop {P Q : Prop} (hP : P) (hQ : Q) : True := by
  have hPQ := And.intro hP hQ
  sorry
theorem andIntroduction {P Q : Prop} (hP : P) (hQ : Q) : P ∧ Q := by
  apply And.intro
  sorry
  sorry
theorem andEliminationTop {P Q : Prop} (hPQ : P ∧ Q) : True := by
  have hP := hPQ.left
  sorry
theorem andEliminationBottom {P Q : Prop} : P := by
  apply And.left (a := P) (b := Q)
  sorry

theorem orIntroductionTop {P Q : Prop} (hP : P) : True := by
  have mmm : P ∨ Q := Or.inl hP
  sorry
theorem orIntroductionBottom {P Q : Prop} : P ∨ Q := by
  apply Or.inl
  sorry
theorem orEliminationTop {P Q : Prop} (pq : P ∨ Q) : True := by
  cases' pq with m n
  sorry
  sorry
theorem orEliminationBottom {P Q : Prop} : True := by
  apply Or.elim (a := P) (b := Q)
  sorry
  sorry
  sorry

