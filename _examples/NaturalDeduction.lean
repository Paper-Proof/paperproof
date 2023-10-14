import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Parity
import Mathlib.Data.List.Chain
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith
import Std.Data.Int.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Algebra.GCDMonoid.Multiset
import Lean
import Paperproof

open Lean Lean.Elab

--------- NATURAL DEDUCTION: basic building blocks ---------

-- CONJUNCTION
theorem andIntroductionTop {A B : Prop} (h1 : A) (h2 : B) : True := by
  have h := And.intro h1 h2
theorem andIntroductionBottom {A B : Prop} (h1 : A) (h2 : B) : A ∧ B := by
  apply And.intro
theorem andEliminationTop {A B : Prop} (h : A ∧ B) : True := by
  have h1 := h.left
theorem andEliminationBottom {A B : Prop} : A := by
  apply And.left (a := A) (b := B)

-- DISJUNCTION
theorem orIntroductionTop {A B : Prop} (h : A) : True := by
  have ab : A ∨ B := Or.inl h
theorem orIntroductionBottom {A B : Prop} : A ∨ B := by
  apply Or.inl
theorem orEliminationTop {A B : Prop} (h : A ∨ B) : True := by
  cases' h with a b
theorem orEliminationBottom {A B : Prop} : True := by
  apply Or.elim (a := A) (b := B)

-- IMPLICATION
theorem arrowIntroductionTop {A B : Prop} (b : B) : True := by
  let h := λ a : A => b
theorem arrowIntroductionBottom {A B : Prop} : A → B := by
  intro a
theorem arrowEliminationTop {A B : Prop} (a : A) (ab : A → B) : True := by
  let h := ab a
theorem arrowEliminationBottom {A B : Prop} (a : A) : B := by
  revert a

-- THE UNIVERSAL QUANTIFIER
theorem forallIntroductionBottom {α : Type} {A : α → Prop} : ∀ y, A y := by
  intro x
theorem forallEliminationTop {α : Type} {A : α → Prop}
  (h : ∀ x, A x) (t : α) : True := by
  let s := h t
-- Corresponding Top & Bottom rules are hard to achieve with tactics, there are no tactics for turning free vars into foralls afaik

-- THE EXISTENTIAL QUANTIFIER
theorem existsIntroductionTop {α : Type} {A : α → Prop} {t: α} (h : A t) : True := by
  have h2 : ∃ x, A x := Exists.intro t h
theorem existsIntroductionBottom {α : Type} {A : α → Prop} {t: α} : ∃ x, A x := by
  apply Exists.intro (w := t)
theorem existsEliminationTop {α : Type} {A : α → Prop} (h : ∃ x, A x) : True := by
  cases' h with y h1
theorem existsEliminationBottom {α : Type} {A : α → Prop} (h : ∃ x, A x) (t : α) : A t := by
  apply Exists.elim (p := A)
-- WILD versions are veridical reproduction of what we see in logic textbooks. In lean we'll be using normal versions though.
theorem existsEliminationTopWILD {α : Type} {B : Prop} {A : α → Prop} (h : ∃ x, A x) (hi : ∀ y, A y → B) : True := by
  cases' h with s h2
  let h3 := hi s h2
theorem existsEliminationBottomWILD {α : Type} {A : α → Prop} {B: Prop} : B := by
  apply Exists.elim (p := A)
  sorry
  intro y

--------- NATURAL DEDUCTION: full-fledged theorems ---------

theorem page66 {α : Type} {A : α → Prop} {B : α → Prop}
: (∀x, A x) → ((∀x, B x) → (∀y, (A y ∧ B y))) := by
  intro hi
  intro hello
  intro b
  apply And.intro
  exact hi b
  exact hello b

-- We can interpret th natural deduction tree as either page66_evenOdd_TOP or page66_evenOdd_BOTTOM
theorem page66_evenOdd_TOP {even : ℕ → Prop} {odd : ℕ → Prop} (h1: ∀n, (¬ even n → odd n)) : ∀ n, (even n) ∨ (odd n) := by
  intro x

  have h := Classical.em (even x)
  cases' h with hi hello
 
  left
  exact hi

  right
  exact h1 x hello
-- TODO:tomorrow hm I think this is the most correct interpretation
theorem page66_evenOdd_BOTTOM {even : ℕ → Prop} {odd : ℕ → Prop} (h1: ∀n, (¬ even n → odd n)) : ∀ n, (even n) ∨ (odd n) := by
  intro x
  have h := Classical.em

  apply Or.elim (a := even x) (b := ¬ even x)
  apply h

  intro hi
  left
  exact hi

  intro hello
  right
  exact h1 x hello



  

lemma th1 (M N : Prop) (h: M → N) (m: M) : N := h m
lemma th2 (M N : Prop) (h: M ∧ N) : M := h.left
lemma th3 (M N : Prop) (h: M ∧ N) : N := h.right

theorem bottomUp {A B C : Prop} : (A → (B → C)) → (A ∧ B → C) := by
  intros abc ab
  apply (th1 B C)
  apply (th1 A (B → C))
  exact abc

  apply th2 A B
  exact ab

  apply th3 A B
  exact ab


theorem topDown {A B C : Prop} : (A → (B → C)) → (A ∧ B → C) := by
  intros abc ab
  have a := ab.left
  have b := ab.right
  have bc := abc a
  have h := bc b
  exact h
