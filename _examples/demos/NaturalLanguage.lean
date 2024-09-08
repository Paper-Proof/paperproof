import Mathlib.Data.Set.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.GCongr
import Paperproof
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Cases
import Mathlib.Algebra.Order.Field.Basic

/-
This is a proof from "Figure 1: Spivak’s corollary and proof"
from "How to write a 21st century Proof" by Leslie Lamport
(https://lamport.azurewebsites.net/pubs/proof.pdf).

Generally, we want to compare Paperpoof vs structured proofs,
but I didn't get to it yet.

For now, this shows how to convert natural language proofs into Paperproof notation.
-/

theorem fake_mean_value_theorem {i1 i2 : ℝ} (f : ℝ → ℝ) (h : i1 < i2) : ∃ c ∈ Set.Icc i1 i2, deriv f c = (f i2 - f i1) / (i2 - i1) := by
  sorry

theorem interval_child { a b c i1 i2 : ℝ } (aInI: a ∈ Set.Icc i1 i2) (bInI: b ∈ Set.Icc i1 i2) (cInAB: c ∈ Set.Icc a b) : c ∈ Set.Icc i1 i2 := by
  let abInI := Set.Icc_subset_Icc aInI.1 bInI.2
  exact Set.mem_of_mem_of_subset cInAB abInI

theorem posTop {n m : ℝ} (dPos: n > 0) (divPos: m / n > 0) : m > 0 := by
  exact (div_pos_iff_of_pos_right dPos).mp divPos

theorem corollary_increasing_function (f : ℝ → ℝ) (i1 i2 : ℝ) :
  (∀ x ∈ Set.Icc i1 i2, (deriv f x) > 0) →
  (∀ x ∈ Set.Icc i1 i2, ∀ y ∈ Set.Icc i1 i2, x < y → f x < f y) := by
  intros fact a aIn b bIn ab

  let meanValueTheorem := fake_mean_value_theorem f ab
  rcases meanValueTheorem with ⟨c, ⟨ cIn, derivEquals ⟩ ⟩

  have derivPos := fact c (interval_child aIn bIn cIn)

  have quotientPos : (f b - f a) / (b - a) > 0 := by
    rw [derivEquals] at derivPos
    exact derivPos

  exact lt_add_neg_iff_lt.mp (posTop (sub_pos.mpr ab) quotientPos)
