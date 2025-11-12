import Mathlib.Algebra.GCDMonoid.Multiset
import Mathlib.Data.Real.Basic
import Lean
import Paperproof

theorem apply (a b : ℝ) : a = b := by
  apply le_antisymm

theorem have_ (a b : ℝ) (h1 : a ≤ b) (h2 : b ≤ a) : True := by
  have hi := le_antisymm h1 h2

theorem intro : ∀ (N : ℕ), ∃ M, N + N = M := by
  intro n

theorem rw (a b : ℕ) (h1: a = b) : (10 * a = 666) := by
  rw [h1]

theorem by_contra_ (m : ℕ) : 2 ≤ m := by
  by_contra h

theorem use : ∃ x : Nat, x = 5 := by
  use 42

theorem induction (n : ℕ) : Nat.mul 0 n = 0 := by
  induction n

