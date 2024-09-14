import Mathlib.Tactic.Cases
import Mathlib.Tactic.Use
import Mathlib.Data.Set.Basic
import Paperproof

-- 1. What can be do to `_ → _` goal?
-- 2. What can we do to `_ ∧ _` hypothesis?
theorem top : a ∧ b → a := by
  sorry

-- 1. What can be do to `_ → _` goal?
-- 2. What can we do to `_ ∧ _` goal?
theorem bottom : a → b → a ∧ b := by
  sorry

-- 1. Variable scopes
theorem commutativityOfIntersections
(s t : Set Nat) : s ∩ t = t ∩ s := by
  ext x
  apply Iff.intro

  intro h1
  rw [Set.mem_inter_iff, and_comm] at h1
  exact h1

  -- intro h2
  -- rw [Set.mem_inter_iff, and_comm] at h2
  -- exact h2


-- Very physical actions
-- Very few moves to memorize
