import Mathlib.Data.Set.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.GCongr
import Paperproof

--------------------------- Nice Things ---------------------------

-- 1. What hypothesis did the `gcongr`/`omega`/`simp`/etc. tactic use??
example {m n : ℤ} (h1 : m + 3 ≤ 2 * n - 1) (h2 : n ≤ 5) : m + 3 ≤ 9 := by
  calc
    m + 3 ≤ 2 * n - 1 := by gcongr
    _     ≤ 2 * 5 - 1 := by omega

-- 2. Typical mathlib proof
--    (rw[] sequences expanded)
theorem finFunctionFinEquiv_single11 {m n : ℕ} [NeZero m] (i : Fin n) (j : Fin m) : (finFunctionFinEquiv (Pi.single i j) : ℕ) = j * m ^ (i : ℕ) := by
  rw [finFunctionFinEquiv_apply, Fintype.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · rintro x hx
    rw [Pi.single_eq_of_ne hx, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_mul]


-- 3. We can see exactly what path was taken by tactic combinators
theorem combs (p q r : Prop) (hp : p)
  : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  repeat (first | apply And.intro | apply Or.inl; assumption | apply Or.inr | assumption)

-- 4. Copy for LLM
theorem append_assoc {α : Type} (a b c : List α) : (a ++ b) ++ c = a ++ (b ++ c) := by
  induction a with
  | nil => simp only [List.nil_append]
  | cons x xs ih =>
    simp [List.cons_append, ih]


--------------------------- Real Projets ---------------------------

-- 2. Carleson:933: Mode:all-tactics + create snapshot
-- 3. Carleson:933: Mode:single-tactic

-- two ways to show diffs: look at red/green highlights + click 3 TIMES
-- or simply display 2 things after each other


