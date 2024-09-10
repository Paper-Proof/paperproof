import Mathlib.Data.Set.Basic
import Paperproof

-- Note to self: do not explain anything, just type the tactics
theorem commutativityOfIntersections
(s t : Set Nat) : s ∩ t = t ∩ s := by
  sorry
  -- ext x
  -- apply Iff.intro

  -- intro h1
  -- rw [Set.mem_inter_iff, and_comm] at h1
  -- exact h1

  -- intro h2
  -- rw [Set.mem_inter_iff, and_comm] at h2
  -- exact h2
