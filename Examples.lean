import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith
import Std.Data.Int.Basic
import PaperProof
import Mathlib.Data.Set.Basic

import Lean

theorem th11 : ∀ (N : ℕ), ∃ M, N + N = M := by {
  intro n
  exact ⟨ n + n, rfl ⟩ 
}

theorem infinitude_of_primes : ∀ N, ∃ p, p ≥ N ∧ Nat.Prime p := by
  intro N

  let M := Nat.factorial N + 1
  let p := Nat.minFac M

  have pp : Nat.Prime p := by {
    sorry
  }
  have ppos: p ≥ N := by
    apply by_contradiction
    intro pln
    have h₁ : p ∣ Nat.factorial N := by  {
      apply pp.dvd_factorial.mpr
      exact le_of_not_ge pln
    }
    have h₂ : p ∣ Nat.factorial N + 1 := Nat.minFac_dvd M
    have h : p ∣ 1 := (Nat.dvd_add_right h₁).mp $ h₂
    exact Nat.Prime.not_dvd_one pp h
  exact ⟨ p, ppos, pp ⟩

-- TODO: Parser doesn't work for this theorem yet
-- At the current stage of the proof, it should render like this: https://gcdnb.pbrd.co/images/ElpHkUUB5HjM.jpg?o=1
-- 1) "tactic rw" changing hypothesis should work
-- 2) Destructuring in have's intro's rintro's should work
-- https://github.com/leanprover/lean4/blob/8a302e6135bc1b0f1f2901702664c56cd424ebc2/src/Init/Tactics.lean
theorem irrational_sqrt_2 : ¬ ∃ (q : ℚ), q * q = 2 := by
  apply not_exists.mpr
  intro ⟨n, d, _, coprime⟩ h
  have h₁ : n * n = 2 * d * d:= by
    rw [← Rat.normalize_self 2, Rat.mul_def, Rat.normalize_eq_iff] at h
    simp at h
    linarith
  rw [← Int.natAbs_mul_self'] at h₁
  have ⟨n', h₂⟩ : ∃ n', n.natAbs = 2 * n' := by
    have hm : Even (2 * d * d) := by
      rw [Nat.even_mul, Nat.even_mul]
      left; left
      trivial
    sorry
  have ⟨d', h₃⟩ : ∃ d', d = 2 * d' := by sorry
  rw [h₂, h₃] at h₁
  have r : (∀ k, ¬ 2 * k = 1) := by sorry 
  rw [Nat.coprime_iff_gcd_eq_one, h₂, h₃] at coprime
  rw [Nat.gcd_mul_left] at coprime
  apply r _ coprime

theorem mini_example : true = true := by
  have ⟨a, b⟩: ∃ c, c = 2 := by sorry
  have ⟨c, d⟩: ∃ e, e = 2 := ⟨2, rfl⟩ 
  exact rfl

example : (a = b) → (b = c) → (c = d)  → (a = d) := by
  intro ab bc cd
  rw [ab, bc, cd] 

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp

theorem commutativityOfIntersections (s t : Set Nat) : s ∩ t = t ∩ s := by
  ext x
  apply Iff.intro
  intro h1
  rw [Set.inter_comm]
  exact h1
  intro h1
  rw [Set.inter_comm]
  exact h1

example : a ∧ b → m ∧ n → a ∧ b := by
  intro hi
  intro hello
  apply And.intro
  -- cases hi
  clear hi
  sorry
  sorry
  -- exact hi.left

example (f : Nat → Nat) (a : Nat) (h : a + 0 = 0) : f a = f 0 := by
  rw [Nat.add_zero] at h
  rw [h]

example : (a = b) → (b = c) → (c = d)  → (a = d) := by
  intro ab
  intro bc
  intro cd
  -- rw [ab, bc, cd] 
  rw [ab]
  rw [bc]
  rw [cd]

theorem simple : ∀ (N : ℕ), ∃ M, N + N = M := by
  intro n
  use n + n

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro hello
  intro hi
  intro aaa
  cases aaa
  
  left
  apply hello
  assumption

  right
  apply hi
  assumption

example (α : Type) (s t : Set α) : s ∩ t = t ∩ s := by
  ext x
  simp only [Set.mem_inter_iff]
  apply Iff.intro
  
  rintro ⟨xs, xt⟩
  exact ⟨xt, xs⟩
  
  sorry

theorem theorem_7 (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  intro h
  cases h.right
  exact Or.inl ⟨h.left, ‹q›⟩

  exact Or.inr ⟨h.left, ‹r›⟩
  intro h
  cases h

  rename_i hpq
  exact ⟨hpq.left, Or.inl hpq.right⟩

  rename_i hpr
  exact ⟨hpr.left, Or.inr hpr.right⟩
  
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  intro h
  cases h.right
  exact Or.inl ⟨h.left, ‹q›⟩
