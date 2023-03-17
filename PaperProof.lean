import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith
import Std.Classes.Dvd

import Lean
open Lean Widget

theorem infinitude_of_primes : ∀ N, ∃ p, p ≥ N ∧ Nat.Prime p := by
  intro N
  
  let M := Nat.factorial N + 1
  let p := Nat.minFac M

  use p
  
  have pp : Nat.Prime p := by {
    have minFac_prime := @Nat.minFac_prime M
    apply minFac_prime
    have := Nat.factorial_pos N
    linarith
  }
  have ppos: p ≥ N := by {
    apply by_contradiction
    intro pln
    have h₁ : p ∣ Nat.factorial N := by  {
      refine pp.dvd_factorial.mpr ?_
      exact le_of_not_ge pln
    }
    have h₂ : p ∣ Nat.factorial N + 1 := by apply Nat.minFac_dvd
    have sp : {a : Nat} → (p ∣ Nat.factorial N + a) → p ∣ a := (Nat.dvd_add_right h₁).mp
    have h : p ∣ 1 := sp h₂
    apply Nat.Prime.not_dvd_one pp h
  }
  exact ⟨ ppos, pp ⟩

def g : Nat → Nat → Int := fun n m => n + m 
def f : Nat → Int := g 3

def my_id (n : Nat) := n

def functions_example : True := by
  let y := f 4
  
  exact True.intro


def dist (x y : Int): Nat := (x - y).natAbs
def f'(x : Int): Int := x + 1

theorem limit:
  ∃ L, ∀ ε, ε > 0 → ∃ N, ∀ n, n ≥ N → dist (f' n) L < ε := by sorry

theorem using_primes : a → a := by
  let x := infinitude_of_primes
  let y := limit 

  sorry

theorem exSeq (limit:
  ∃ L, ∀ ε, ε > 0 → ∃ N, ∀ n, n ≥ N → dist (f n) L < ε): 3 < 4 := by
  sorry

/-



-- def list := [∃ L, ∀ ε, ∀ ε > 0, ∃ N, ∀ n, ∀ n ≥ N, dist (f n) L < ε]
-- def list2 := [∀ eps, ∀ ε > 0, ∃ δ, ∃ δ > 0, ∀ x y, ∀ dist x y < δ, dist (f x) (f y) < ε]

theorem ex (limit:∀ ε, ε > 0 → ∃ δ, δ > 0 ∧
(∀ x y, dist x y < δ → dist (f x) (f y) < ε)): 3 < 4 := by
  have ε := 1
  have hε : ε > 0 := by sorry
  have ⟨ δ, ⟨ hδ, st ⟩ ⟩:= limit ε hε

  sorry
-/

@[widget]
def ppWidget: UserWidgetDefinition := {
  name := "Paper proof"
  javascript:= include_str "widget" / "dist" / "paperProof.js"
}

def test (x : ℕ):  ℕ :=
  sorry

-- Check widget wiring
#widget ppWidget .null