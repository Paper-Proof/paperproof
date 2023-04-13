import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith
import TacticTree

import Lean
open Lean Widget
 
theorem infinitude_of_primes : ∀ N, ∃ p, p ≥ N ∧ Nat.Prime p := by
  intro N

  let M := Nat.factorial N + 1
  let p := Nat.minFac M

  have pp : Nat.Prime p := by {
    apply Nat.minFac_prime
    have fac_pos: 0 < Nat.factorial N := Nat.factorial_pos N
    linarith
  }
  have ppos: p ≥ N := by {
    apply by_contradiction
    intro pln
    have h₁ : p ∣ Nat.factorial N := by  {
      refine pp.dvd_factorial.mpr ?_
      exact le_of_not_ge pln
    }
    have h₂ : p ∣ Nat.factorial N + 1 := Nat.minFac_dvd M
    have h : p ∣ 1 := (Nat.dvd_add_right h₁).mp $ h₂
    exact Nat.Prime.not_dvd_one pp h
  }
  exact ⟨ p, ppos, pp ⟩

theorem th : ∀ {a b : Prop}, a ∧ b → b ∧ a := by
  intro a b h
  exact ⟨ h.right, h.left ⟩

structure SomeProps where
  position: Lsp.Position
