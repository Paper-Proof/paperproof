/-
  This is a development file for working with html header.
-/
import Mathlib.Data.Set.Basic
import Paperproof

-- BOTH
example (h : x = 3) (b : y = 3) : x = y := by
  rw [b]
  assumption
  done

-- 2nd
theorem test123 (p : Prop) (hp : p) : p ∧ p := by
  apply And.intro
  exact hp
  exact hp

-- 1st
example (a b c : ℕ) : (a = b) → (b = c) → (a = c) := by
  intros ab bc
  sorry

-- NONE
example : 3 = 3 := by
  have ⟨ p, q ⟩ : (3 = 3) ∧ (4 = 4) := ⟨ by rfl, by rfl ⟩
  rfl
