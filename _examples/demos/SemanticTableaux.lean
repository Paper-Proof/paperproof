import Mathlib.Data.Nat.Prime.Basic
import Paperproof

--------- SEMANTIC TABLEAUX: basic building blocks ---------

theorem simpleAnd (X: Prop) (Y: Prop) (h: X ∧ Y) : False := by
  rcases h with ⟨h1, h2⟩
  all_goals sorry

theorem simpleOr (X: Prop) (Y: Prop) (h: X ∨ Y) : False := by
  rcases h with h1 | h2
  all_goals sorry

theorem simpleThen (X: Prop) (Y: Prop) (h: X → Y) : False := by
  rw [imp_iff_not_or] at h
  rcases h with h1 | h2
  all_goals sorry

theorem simpleNotOr (X: Prop) (Y: Prop) (h: ¬(X ∨ Y)) : False := by
  rw [not_or] at h
  rcases h with ⟨h1, h2⟩
  sorry

theorem simpleNotAnd (X: Prop) (Y: Prop) (h: ¬(X ∧ Y)) : False := by
  rw [not_and_or] at h
  rcases h with h1 | h2
  all_goals sorry

theorem simpleNotThen (X: Prop) (Y: Prop) (h: ¬(X → Y)) : False := by
  rw [Classical.not_imp] at h
  rcases h with ⟨h1, h2⟩
  sorry

theorem simpleForall {α : Type} (φ : α → Prop) (a : α) (h: ∀ x, φ x) : False := by
  let h1 := h a
  sorry

theorem simpleExists {α : Type} (φ : α → Prop) (h: ∃ x, φ x) : False := by
  rcases h with ⟨a, h1⟩
  sorry

theorem simpleNotExists {α : Type} (φ : α → Prop) (a : α) (h: ¬ ∃ x, φ x) : False := by
  rw [not_exists] at h
  let h1 := h a
  sorry

theorem simpleNotForall {α : Type} (φ : α → Prop) (h: ¬ ∀ x, φ x) : False := by
  rw [not_forall] at h
  rcases h with ⟨a, h1⟩
  sorry

--------- SEMANTIC TABLEAUX: full-fledged theorems ---------

-- (See `https://www.umsu.de/trees/#~3(p~2q)~5(~3p~1~3q)` for semantic tableaux)
theorem deMorgan (p : Prop) (q : Prop) : ¬(p ∨ q) → (¬p ∧ ¬q) := by
  -- Creating 1.
  by_contra h1

  -- Creating 2. and 3.
  rw [Classical.not_imp] at h1
  rcases h1 with ⟨h2, h3⟩

  -- Creating 4. and 5.
  rw [not_or] at h2
  rcases h2 with ⟨h4, h5⟩

  -- Creating 6. and 7.
  rw [not_and, imp_iff_not_or] at h3
  rcases h3 with h6 | h7

  -- Close the branch!
  exact h6 h4

  -- Close the branch!
  exact h7 h5

-- (See `https://www.umsu.de/trees/#((p~2q)~1(q~5p))~5p` for semantic tableaux)
theorem manyGoals (p : Prop) (q : Prop) : ((p ∨ q) ∧ (q → p)) → p := by
  -- Creating 1.
  by_contra h1

  -- Creating 2. and 3.
  rw [Classical.not_imp] at h1
  rcases h1 with ⟨h2, h3⟩

  -- Creating 4. and 5.
  rcases h2 with ⟨h4, h5⟩

  -- Creating 6. and 7.
  rw [imp_iff_not_or] at h5
  rcases h5 with h6 | h7

  -- Creating 8. and 9.
  rcases h4 with h8 | h9

  -- Close the branch!
  exact h3 h8

  -- Close the branch!
  exact h6 h9

  -- Close the branch!
  exact h3 h7

-- (See `https://www.umsu.de/trees/#~7x(Px~1Qx)~5~7x(Px)~1~7x(Qx)` for semantic tableaux)
theorem firstOrderLogic {α : Type} (P Q : α → Prop)
: (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x) := by
  by_contra h1

  -- Creating 2. and 3.
  rw [Classical.not_imp] at h1
  rcases h1 with ⟨h2, h3⟩

  -- Creating 4.
  rcases h2 with ⟨a, h4⟩

  -- Creating 5. and 6.
  rcases h4 with ⟨h5, h6⟩

  -- Creating 7. and 8.
  rw [not_and_or] at h3
  rcases h3 with h7 | h8

  -- Creating 9.
  rw [not_exists] at h7
  let h9 := h7 a

  -- Close the branch!
  exact h9 h5

  -- Creating 10.
  rw [not_exists] at h8
  let h10 := h8 a

  -- Close the branch!
  exact h10 h6
