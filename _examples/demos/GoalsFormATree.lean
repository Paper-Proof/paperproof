import Lean.Elab.Tactic
import Paperproof
open Lean Elab Tactic Meta

-- This file shows why Paperproof goals always form a tree.
-- These tactics are taken from "Metaprogramming in Lean" solutions (https://leanprover-community.github.io/lean4-metaprogramming-book/solutions/09_tactics.html).

elab "tactic_1" : tactic => do
  let mvarId ← getMainGoal
  let goalType ← getMainTarget

  let Expr.app (Expr.app (Expr.const `Iff _) a) b := goalType | throwError "Goal type is not of the form `a ↔ b`"

  -- 1. Create new `_`s with appropriate types.
  let mvarId1 ← mkFreshExprMVar (Expr.forallE `xxx a b .default) (userName := Lean.Name.mkSimple "red")
  let mvarId2 ← mkFreshExprMVar (Expr.forallE `yyy b a .default) (userName := Lean.Name.mkSimple "blue")

  -- 2. Assign the main goal to the expression `Iff.intro _ _`.
  mvarId.assign (mkAppN (Expr.const `Iff.intro []) #[a, b, mvarId1, mvarId2])

  -- 3. Report the new `_`s to Lean as the new goals.
  modify fun _ => { goals := [mvarId1.mvarId!, mvarId2.mvarId!] }

elab "tactic_2" : tactic => do
  let some redMvarId ← (← get).goals.findM? (fun mvarId => do
    return (← mvarId.getDecl).userName == `red
  ) | throwError "No mvar with username `red`"
  let some blueMvarId ← (← get).goals.findM? (fun mvarId => do
    return (← mvarId.getDecl).userName == `blue
  ) | throwError "No mvar with username `blue`"

  ---- HANDLE `red` goal
  let Expr.forallE _ redFrom redTo _ := (← redMvarId.getDecl).type | throwError "Goal type is not of the form `a → b`"
  let handyRedMvarId ← withLocalDecl `hA BinderInfo.default redFrom (fun fvar => do
    -- 1. Create new `_`s with appropriate types.
    let mvarId1 ← mkFreshExprMVar redTo MetavarKind.syntheticOpaque `red
    -- 2. Assign the main goal to the expression `fun hA => _`.
    redMvarId.assign (← mkLambdaFVars #[fvar] mvarId1)
    -- just a handy way to return a handyRedMvarId for the next code
    return mvarId1.mvarId!
  )
  -- 3. Report the new `_`s to Lean as the new goals.
  modify fun _ => { goals := [handyRedMvarId, blueMvarId] }

  ---- HANDLE `blue` goal
  let Expr.forallE _ blueFrom _ _ := (← blueMvarId.getDecl).type | throwError "Goal type is not of the form `a → b`"
  -- 1. Create new `_`s with appropriate types.
  -- None needed!
  -- 2. Assign the main goal to the expression `fun hB : q ∧ p => (And.intro hB.right hB.left)`.
  Lean.Meta.withLocalDecl `hB .default blueFrom (fun hB => do
    let body ← Lean.Meta.mkAppM `And.intro #[← Lean.Meta.mkAppM `And.right #[hB], ← Lean.Meta.mkAppM `And.left #[hB]]
    blueMvarId.assign (← Lean.Meta.mkLambdaFVars #[hB] body)
  )
  -- 3. Report the new `_`s to Lean as the new goals.
  modify fun _ => { goals := [handyRedMvarId] }



theorem gradual (p q : Prop) : p ∧ q ↔ q ∧ p := by
  tactic_1
  tactic_2
  sorry


variable (p q : Prop)

-- [this is the initial goal]
example : p ∧ q ↔ q ∧ p :=
  _

-- [proof term after tactic_1]
example : p ∧ q ↔ q ∧ p :=
  Iff.intro _ _

-- [proof term after tactic_2]
example : p ∧ q ↔ q ∧ p :=
  Iff.intro (λ hP => _) (λ hQ => (And.intro hQ.right hQ.left))
