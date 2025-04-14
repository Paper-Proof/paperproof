/-
  This is a development file for checking how `rw`, `rwa`, `nth_rw`, etc. get rendered in Paperproof.
-/
import Mathlib.Tactic
import Paperproof

theorem commutativityOfIntersections
(s t : Set Nat) : s ∩ t = t ∩ s := by
  ext x
  apply Iff.intro
  rw [Set.mem_inter_iff, and_comm]

theorem sss
(s t : Set Nat) : s ∩ t = t ∩ s := by
  ext x
  apply Iff.intro
  erw [Set.mem_inter_iff, and_comm]

theorem www
(s t : Set Nat) : s ∩ t = t ∩ s := by
  ext x
  apply Iff.intro
  rw_mod_cast [Set.mem_inter_iff, and_comm]

theorem ddd
(s t : Set Nat) : s ∩ t = t ∩ s := by
  ext x
  apply Iff.intro
  rwa [Set.mem_inter_iff, and_comm]

example (h : a = 1) : a + a + a + a + a = 5 := by
  nth_rewrite 2 3 [h]

example (a b c : Nat) : (a + b) + c = (b + a) + c := by
  nth_rw 2 [Nat.add_comm]
