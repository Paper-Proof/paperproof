import Mathlib.Data.Set.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.GCongr
import Paperproof

-- PAPERPROOF TUTORIAL

-- 1. Green and yellow hypotheses
example (x : ℕ) (y : ℕ) (a : x = 3) (b : y = 3) : x = y := by
  rw [b]
  assumption

-- 2. What happens when you type stuff
theorem commutativityOfIntersections (s t : Set Nat)
: s ∩ t = t ∩ s := by
  ext x
  apply Iff.intro

  intro h1
  rw [Set.mem_inter_iff, and_comm] at h1
  exact h1

  intro h2
  rw [Set.mem_inter_iff, and_comm] at h2
  exact h2

-- 3. What hypothesis did `simp`/`assumption`/etc. tactic use???
theorem simple_ex (n m : ℕ)
  (h1 : ∀ {a b : Nat}, a + b = b + a)
  (h2 : ∀ {a b : Nat}, a = b + b):
    n + m = m + n := by
  simp [h1, h2]

-- 4. `calc` is a transitivity thing (also: again, what hypotheses are used)
example {m n : ℤ} (h1 : m + 3 ≤ 2 * n - 1) (h2 : n ≤ 5) : m + 3 ≤ 9 := by
  calc
    m + 3 ≤ 2 * n - 1 := by gcongr
    _     ≤ 2 * 5 - 1 := by gcongr; norm_num

-- 5. rewrites are nicely nested under each other
example (a b c d e f : ℕ) (h : b = e) (h₂ : e = d): (a = b) → (b = c) → (e = f) → True := by
  intros ab cd ef
  rw [h, h₂] at *
  trivial

-- 6. Typical mathlib proof
--    (rw[] sequences expanded, nice .dependsOn arrows)
--    (compact mode, collapse a box)
theorem finFunctionFinEquiv_single11 {m n : ℕ} [NeZero m] (i : Fin n) (j : Fin m) : (finFunctionFinEquiv (Pi.single i j) : ℕ) = j * m ^ (i : ℕ) := by
  rw [finFunctionFinEquiv_apply, Fintype.sum_eq_single i, Pi.single_eq_same]
  rintro x hx
  rw [Pi.single_eq_of_ne hx, Fin.val_zero', zero_mul]

-- 7. Any `cases`/`induction` has a uniform interface
namespace OurInductives
variable (SomeGoal: Prop)

inductive Prod (α : Type u) (β : Type v)
  | mk : α → β → Prod α β
theorem prod (hi: Prod Nat Nat) : SomeGoal := by
  cases' hi with a b
  sorry

inductive Sum (α : Type u) (β : Type v) where
  | inl : α → Sum α β
  | inr : β → Sum α β
theorem sum (hi: Sum Nat Nat) : SomeGoal := by
  cases' hi with a b
  sorry; sorry

inductive Random where
  | hi: ℕ → String → Random
  | hello: (2 + 2 = 4) → Random
  | wow: Random
theorem casesRandom (h: Random) : SomeGoal := by
  cases' h with a b c
  sorry; sorry; sorry

-- 8. We can see exactly what path was taken by tactic combinators
theorem combs (p q r : Prop) (hp : p)
  : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  repeat (first | apply And.intro | apply Or.inl; assumption | apply Or.inr | assumption)
  done
