import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Parity
import Mathlib.Data.List.Chain
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith
import Std.Data.Int.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Algebra.GCDMonoid.Multiset
import Lean
import Paperproof

example : 4 = 4 := by
  have p : 3 = 3 := rfl
  simp

example (h : x = 3) (b : y = 3) : x = y := by
  rwa [b]

example : 3 = 3 := by
  have ⟨ p, q ⟩ : (3 = 3) ∧ (4 = 4) := ⟨ by rfl, by rfl ⟩
  rfl

theorem simple_ex (n m : ℕ)
  (h1 : ∀ {a b : Nat}, a + b = b + a)
  (h2 : ∀ {a b : Nat}, a = b + b):
    n + m = m + n := by
  simp [h1, h2]

example {m n : ℤ} (h1 : m + 3 ≤ 2 * n - 1) (h2 : n ≤ 5) : m ≤ 6 := by
  have h3 := calc
      m + 3 ≤ 2 * n - 1 := by gcongr
      _ ≤ 2 * 5 - 1 := by gcongr
      _ = 9 := by norm_num
  clear h1 h2
  linarith

namespace OurInductives
inductive Prod (α : Type u) (β : Type v)
  | mk : α → β → Prod α β
inductive Sum (α : Type u) (β : Type v) where
  | inl : α → Sum α β
  | inr : β → Sum α β

theorem sum (hi: Sum Nat Nat) : True := by
  cases' hi with a b
  sorry; sorry
theorem prod (hi: Prod Nat Nat) : True := by
  cases' hi with a b
  sorry

open Lean Elab in
theorem infoTree (hi: InfoTree) : True := by
  cases' hi
  sorry; sorry; sorry
end OurInductives


theorem th11 : ∀ (N : ℕ), ∃ M, N + N = M := by {
  intro n
  exact ⟨ n + n, rfl ⟩
}

example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px =>
    sorry
    -- apply Exists.intro



theorem infinitude_of_primes : ∀ N, ∃ p, p ≥ N ∧ Nat.Prime p := by
  intro N

  let M := Nat.factorial N + 1
  let p := Nat.minFac M

  have pp : Nat.Prime p := by
    apply Nat.minFac_prime
    have fac_pos: 0 < Nat.factorial N := by
      exact Nat.factorial_pos N
    linarith

  have ppos: p ≥ N := by
    apply by_contradiction
    intro pln
    have h₁ : p ∣ Nat.factorial N := by
      apply pp.dvd_factorial.mpr
      exact le_of_not_ge pln
    have h₂ : p ∣ Nat.factorial N + 1 := Nat.minFac_dvd M
    have h : p ∣ 1 := (Nat.dvd_add_right h₁).mp $ h₂
    exact Nat.Prime.not_dvd_one pp h
  exact ⟨ p, ppos, pp ⟩

theorem irrational_sqrt_2 : ¬ ∃ (q : ℚ), q * q = 2 := by
  apply not_exists.mpr
  intro ⟨n, d, _, coprime⟩ h
  have h₁ : n * n = 2 * d * d:= by
    rw [← Rat.normalize_self 2, Rat.mul_def, Rat.normalize_eq_iff] at h
    simp at h
    sorry
    -- linarith
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

example (p : Prop) (hp : p) : p := by
  exact hp

theorem test123 (p : Prop) (hp : p) : p ∧ p := by
  apply And.intro
  exact hp
  exact hp

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp







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

example : (a = b) → (b = c) → (c = d) → (a = d) := by
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
  intro hi
  intro wow
  intro hm
  cases' hm with p q
  left
  exact hi p
  right



example (α : Type) (s t : Set α) : s ∩ t = t ∩ s := by
  ext x
  simp only [Set.mem_inter_iff]
  apply Iff.intro

  rintro ⟨xs, xt⟩
  exact ⟨xt, xs⟩



theorem theorem_7 (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  intro xxx
  cases' xxx with hp hqr
  cases' hqr with hq hr
  left
  -- apply And.intro
  -- exact hp
  -- exact hq

  -- apply And.intro hp hq

  exact And.intro hp hq

  right
  exact And.intro hp hr

  intro wow
  apply And.intro
  cases' wow with hm heh
  exact hm.left
  exact heh.left
  cases' wow with a b
  left
  exact a.right
  right
  exact b.right










example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  intro h
  cases h.right
  { apply Or.inl; exact ⟨h.left, ‹q›⟩ }
  { exact Or.inr ⟨h.left, ‹r›⟩ }
  sorry


example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  intro wow
  cases' wow with a b
  cases' b with hQ hR
  left
  exact And.intro a hQ
  sorry
  sorry



example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  sorry

-- example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by


example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  have hehe : true := by trivial
  sorry


example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  intro hi
  cases' hi with P QR
  cases' QR with Q R
  left
  exact And.intro P Q
  right
  apply And.intro
  assumption
  assumption
  intro well
  apply And.intro
  cases' well with m n
  exact m.left
  exact n.left
  cases' well  with m n
  left
  exact m.right
  right
  exact n.right




example (a b c : ℕ) : (a = b) → (b = c) → (a = c) := by
  intros ab bc
  /-
  a b c : ℕ
  ab : a = b
  bc : b = c
  ⊢ a = c
  -/
  subst bc
  /-
  a b : ℕ
  ab : a = b
  ⊢ a = b
  -/
  sorry

theorem small_irrational : ¬ ∃ (q : ℚ), q * q = 2 := by
  apply not_exists.mpr
  intro ⟨n, d, _, coprime⟩ h
  have ⟨n', h₂⟩ : ∃ n', n.natAbs = 2 * n' := by sorry
  have ⟨d', h₃⟩ : ∃ d', d = 2 * d' := by sorry
  have h₁ : n * n = 2 * d * d:= by sorry
  rw [← Int.natAbs_mul_self'] at h₁
  rw [h₂, h₃] at h₁
  have r : (∀ k, ¬ 2 * k = 1) := by sorry
  rw [Nat.coprime_iff_gcd_eq_one, h₂, h₃] at coprime
  rw [Nat.gcd_mul_left] at coprime
  apply r _ coprime

example (a b c d e f : ℕ) (h : b = e) (h₂ : e = d): (a = b) → (b = c) → (e = f) → True := by
  intros ab cd ef
  rw [h, h₂] at *
  trivial

example (a b : Prop) : a ∧ b → b ∧ a := by
  intro ab
  cases ab
  apply And.intro <;> assumption

-- Doesn't work currently
example (p q : Prop) (hep : e = p) : p ∨ q → q ∨ e := by
  intro h
  cases h with rw[hep]
  | inl hppp =>
      apply Or.inr
      exact hppp
  | inr hqqq => apply Or.inl; exact hqqq

example (l : List α) : (∃ x, x ∈ l) ∨ (l = []) := by
  match l with
  | [] => apply Or.inr; rfl
  | a :: ln => apply Or.inl; use a; apply List.mem_cons_self

theorem mem_split {a : α} {as : List α} (h : a ∈ as) : ∃ s t, as = s ++ a :: t := by
  induction as with
  | nil          => cases h
  | cons b bs ih => cases h with
    | head bs => exact ⟨[], ⟨bs, rfl⟩⟩
    | tail someVar h =>
      match ih h with
      | ⟨s, ⟨t, h₂⟩⟩ => exact ⟨b :: s, ⟨t, h₂ ▸ rfl⟩⟩

theorem mem {a : α} {as : List α} (h : a ∈ as) : ∃ s t, as = s ++ a :: t := by
  induction as with
  | nil => cases h
  | cons m mm => sorry

example (p q : Prop) : p → q := by
  have t : true = true := by trivial
  sorry

example (a : Prop) : a → a := by
  have pp : a = a ∧ a = a := ⟨ by rfl, by rfl ⟩
  sorry

example (h : p = q) : p ∨ q → p := by
  intro porq
  cases porq
  clear h
  sorry
  sorry

-- Example with a grid any multi-out goals
example (p q r s : Prop) (h : q = s) : p ∧ q → r ∧ s → true := by
  intros hpq
  cases' hpq with hp hq
  rewrite [h] at hq
  intros hrs
  cases' hrs with hr hs
  trivial

example (p q r s : Prop) : p ∧ q → r ∧ s → true := by
  intros hpq hrs
  cases hpq
  cases hrs
  trivial


example : a ∧ b → a := by
  intro hab
  cases hab
  assumption

open List

theorem chain'_append :
    ∀ {l₁ l₂ : List α},
      Chain' R (l₁ ++ l₂) ↔ Chain' R l₁ ∧ Chain' R l₂ ∧ ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, R x y := by
    intros l1 l2
    match l1, l2 with
    | [], l => simp
    | [a], l => simp [chain'_cons', and_comm]
    | a :: b :: l₁, l₂ =>
      rw [cons_append, cons_append, chain'_cons, chain'_cons, ← cons_append, chain'_append,
        and_assoc]
      simp


theorem dojo4_uncombined (p q r : Prop) (hp : p)
  : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  repeat (first | apply And.intro | apply Or.inl; assumption | apply Or.inr | assumption)

-- 1. `apply Or.inl; assumption` is tried, but fails on `assumption`
-- 2. `apply Or.inr; assumption` is tried, and succeeds
example (p q : Prop) (hq : q) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption


-- before
-- pqr: Prop
-- ⊢ p ∧ (q ∨ r) ↔ p ∧ q ∨ p ∧ r

-- after
-- pqr: Prop
-- ⊢ p ∧ (q ∨ r) → p ∧ q ∨ p ∧ r
-- pqr: Prop
-- ⊢ p ∧ q ∨ p ∧ r → p ∧ (q ∨ r)

example (p q r: Prop) : p ∧ (q ∨ r) ↔ p ∧ q ∨ p ∧ r := by
  refine' ⟨_, fun h => _⟩
  sorry
