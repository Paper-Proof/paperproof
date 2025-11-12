import Mathlib.Data.Set.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.GCongr
import Paperproof

-- 1. What hypothesis did `simp`/`assumption`/etc. tactic use???
theorem simple_ex (n m : ℕ)
  (h1 : ∀ {a b : Nat}, a + b = b + a)
  (h2 : ∀ {a b : Nat}, a = b + b):
    n + m = m + n := by
  simp [h1, h2]

-- 2. `calc` is a transitivity thing
--    (also: again, shows what hypotheses are used)
example {m n : ℤ} (h1 : m + 3 ≤ 2 * n - 1) (h2 : n ≤ 5) : m + 3 ≤ 9 := by
  calc
    m + 3 ≤ 2 * n - 1 := by gcongr
    _     ≤ 2 * 5 - 1 := by omega

-- 3. Rewrites are nicely nested under each other
example (a b c d e f : ℕ) (h : b = e) (h₂ : e = d): (a = b) → (b = c) → (e = f) → True := by
  intros ab cd ef
  rw [h, h₂] at *
  trivial

-- 4. Typical mathlib proof
--    (rw[] sequences expanded)
theorem finFunctionFinEquiv_single11 {m n : ℕ} [NeZero m] (i : Fin n) (j : Fin m) : (finFunctionFinEquiv (Pi.single i j) : ℕ) = j * m ^ (i : ℕ) := by
  rw [finFunctionFinEquiv_apply, Fintype.sum_eq_single i, Pi.single_eq_same]
  rintro x hx
  rw [Pi.single_eq_of_ne hx, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_mul]

-- 5. Any `cases`/`induction` has a uniform interface
namespace OurInductives
variable (SomeGoal: Prop)

inductive Prod (α : Type u) (β : Type v)
  | mk : α → β → Prod α β
theorem prod (hi: Prod Nat Nat) : SomeGoal := by
  rcases hi with ⟨a, b⟩
  sorry

inductive Sum (α : Type u) (β : Type v) where
  | inl : α → Sum α β
  | inr : β → Sum α β
theorem sum (hi: Sum Nat Nat) : SomeGoal := by
  rcases hi with x | y
  sorry; sorry

inductive Random where
  | hi: ℕ → String → Random
  | hello: (2 + 2 = 4) → Random
  | wow: Random
theorem casesRandom (h: Random) : SomeGoal := by
  rcases h with ⟨a, b⟩ | ⟨c⟩
  sorry; sorry; sorry

-- 6. We can see exactly what path was taken by tactic combinators
theorem combs (p q r : Prop) (hp : p)
  : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  repeat (first | apply And.intro | apply Or.inl; assumption | apply Or.inr | assumption)

--------------------------- OPTIONS ---------------------------

-- 1. "Zoom in", "Zoom out"
-- 2. "Compact Horizontally"
-- 3. "Compact Tactics" (won't do anything here, but useful for mathlib)
-- 4. "Hide Goal Names"
-- 5. "Always Green Hypotheses"
-- 6. "Collapse box"
theorem append_assoc {α : Type} (a b c : List α) : (a ++ b) ++ c = a ++ (b ++ c) := by
  induction a with
  | nil => simp
  | cons x xs ih =>
    simp [List.cons_append, ih]
