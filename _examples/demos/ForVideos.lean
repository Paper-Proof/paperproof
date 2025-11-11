import Mathlib.Data.Set.Basic
import Paperproof

-- Welcome to paperproof!
-- You are at the correct place.
--
-- 1. Wait for 3 minutes, Lean is automatically loading for you now.
-- 2. Click on the Paperproof icon above.
-- 3. Click on any line in this proof.
theorem commutativityOfIntersections
(s t : Set Nat) : s ∩ t = t ∩ s := by
  ext x
  apply Iff.intro

  intro h1
  rw [Set.mem_inter_iff, and_comm] at h1
  exact h1

  intro h2
  rw [Set.mem_inter_iff, and_comm] at h2
  exact h2
