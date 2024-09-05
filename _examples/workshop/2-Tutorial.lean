import Mathlib.Tactic.Cases
import Mathlib.Tactic.Use
import Paperproof

-- 1. What can be do to `_ → _` goal?
-- 2. What can we do to `_ ∧ _` hypothesis?
theorem top : a ∧ b → a := by
  sorry
  -- intro AB
  -- cases' AB with A B
  -- exact A

-- 1. What can be do to `_ → _` goal?
-- 2. What can we do to `_ ∧ _` goal?
theorem bottom : a → b → a ∧ b := by
  sorry
  -- intros hA hB
  -- apply And.intro
  -- exact hA
  -- exact hB

-- 1. What can we do to `∃ ~, ~` hypothesis?
-- 2. What can we do to `∃ ~, ~` goal?
theorem both (p q : Nat → Prop) (h: ∃ x, p x) : ∃ x, p x ∨ q x := by
  sorry
  -- cases' h with xxx b
  -- apply Exists.intro VS apply Exists.intro xxx
  -- left
  -- exact b

-- Very physical actions
-- Very few moves to memorize
