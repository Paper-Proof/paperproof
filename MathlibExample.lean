import Mathlib.Algebra.BigOperators.Multiset.Lemmas
import Mathlib.Algebra.Group.Pi
import Mathlib.Algebra.GroupPower.Lemmas
import Mathlib.Algebra.Hom.Equiv.Basic
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Multiset.Powerset
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Algebra.BigOperators.Basic
import Paperproof

theorem prod_congr_set {α : Type} [CommMonoid α] {β : Type} [fb: Fintype β] (s : Set β)
[DecidablePred (· ∈ s)] (f : β → α) (g : s → α) (w : ∀ (x : β) (h : x ∈ s), f x = g ⟨x, h⟩)
(w' : ∀ x : β, x ∉ s → f x = 1) : Finset.univ.prod f = Finset.univ.prod g := by
  rw [← @Finset.prod_subset _ _ s.toFinset Finset.univ f _ (by simp)]

  rewrite [Finset.prod_subtype]

  apply Finset.prod_congr rfl
  exact fun ⟨x, h⟩ _ => w x h
  simp

  rintro x _ h
  exact w' x (by simpa using h)
