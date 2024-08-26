import Mathlib.Data.Set.Basic
import Paperproof

theorem commutativityOfIntersections
(s t : Set Nat) : s ∩ t = t ∩ s := by
  ext x
  apply Iff.intro
