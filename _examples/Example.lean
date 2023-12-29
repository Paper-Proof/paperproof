-- This is the example we always use in demos&videos
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Equiv.Fin


import Paperproof






theorem blue (s t : Set Nat) : s ∩ t = t ∩ s := by
  ext x
  apply Iff.intro

  intro h1
  rw [Set.mem_inter_iff, and_comm] at h1
  exact h1

  intro h2
  rw [Set.mem_inter_iff, and_comm] at h2
  exact h2



-- fancy .dependsOn for tactics
theorem simple_ex (n m : ℕ)
  (h1 : ∀ {a b : Nat}, a + b = b + a)
  (h2 : ∀ {a b : Nat}, a = b + b):
    n + m = m + n := by
  simp [h1, h2]

-- nice `calc` display showing calc is a transitivity thing

example {m n : ℤ} (h1 : m + 3 ≤ 2 * n - 1) (h2 : n ≤ 5) : m + 3 ≤ 9 := by
  calc
    m + 3 ≤ 2 * n - 1 := by gcongr
    _ ≤ 2 * 5 - 1 := by gcongr
    _ = 9 := by norm_num

-- any `cases`/`induction` has a uniform interface
namespace OurInductives
inductive Prod (α : Type u) (β : Type v)
  | mk : α → β → Prod α β
inductive Sum (α : Type u) (β : Type v) where
  | inl : α → Sum α β
  | inr : β → Sum α β

theorem sum (hi: Sum Nat Nat) : True := by
  cases' hi with a b
  sorry; sorry
theorem prod (hi: Prod Nat Nat) : True := by
  cases' hi with a b
  sorry

inductive Random where
  | hi: ℕ → String → Random
  | hello: (2 + 2 = 4) → Random
  | wow: Random
theorem casesRandom (SomeGoal: Prop) (h: Random) : SomeGoal := by
  cases' h with a b c
  sorry; sorry; sorry


-- rw[] sequences expanded
theorem finFunctionFinEquiv_single11 {m n : ℕ} [NeZero m] (i : Fin n) (j : Fin m) :
    (finFunctionFinEquiv (Pi.single i j) : ℕ) = j * m ^ (i : ℕ) := by
  rw [finFunctionFinEquiv_apply, Fintype.sum_eq_single i, Pi.single_eq_same]
  rintro x hx
  rw [Pi.single_eq_of_ne hx, Fin.val_zero', zero_mul]


-- rewrites are nicely nested under each other

noncomputable def fintypeOfFinsetCardLe {ι : Type*} (n : ℕ) (w : ∀ s : Finset ι, s.card ≤ n) :
    Fintype ι := by
  apply fintypeOfNotInfinite
  intro i
  obtain ⟨s, c⟩ := Infinite.exists_subset_card_eq ι (n + 1)
  specialize w s
  rw [c] at w
  exact Nat.not_succ_le_self n w

example (a b c d e f : ℕ) (h : b = e) (h₂ : e = d): (a = b) → (b = c) → (e = f) → True := by
  intros ab cd ef
  rw [h, h₂] at *
  trivial
