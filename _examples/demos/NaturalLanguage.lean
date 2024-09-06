import Mathlib.Data.Set.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.GCongr
import Paperproof
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Cases

-- This is a proof of "Figure 1: Spivak’s corollary and proof"

theorem fake_mean_value_theorem
  (f : ℝ → ℝ) (i1 i2 : ℝ) (h : i1 < i2) :
  ∃ c ∈ Set.Icc i1 i2,
    deriv f c = (f i2 - f i1) / (i2 - i1) := by
  sorry

theorem corollary_increasing_function (f : ℝ → ℝ) (i1 i2 : ℝ) (h : i1 < i2) :
  (∀ x ∈ Set.Icc i1 i2, (deriv f x) > 0) →
  (∀ x ∈ Set.Icc i1 i2, ∀ y ∈ Set.Icc i1 i2, x < y → f x < f y) := by
  intros fact a aIn b bIn ab

  let meanValueTheorem := fake_mean_value_theorem f a b ab
  rcases meanValueTheorem with ⟨c, ⟨ cIn, derivEquals ⟩ ⟩

  have cIn_i1_i2 : c ∈ Set.Icc i1 i2 := by
    apply Set.mem_of_mem_of_subset cIn
    exact Set.Icc_subset_Icc aIn.1 bIn.2

  have deriv_pos := fact c cIn_i1_i2


  rw [derivEquals] at deriv_pos

  have ba_pos : 0 < b - a
    := sub_pos.mpr ab

  have sss := (div_pos_iff (a := f b - f a) (b := b - a)).mp deriv_pos

  cases' sss with cool great
  cases' cool with what how
  exact sub_pos.mp what

  cases' great with what how
  let nnn := lt_asymm ba_pos
  let fls := nnn how
  exfalso
  exact fls
