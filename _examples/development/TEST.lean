import Paperproof
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Explode

open Set
variable {α β : Type*} {s t : Set α}

-- TEST: rw; exact
theorem TEST_encard_union_le (s t : Set α) : (s ∪ t).encard ≤ s.encard + t.encard := by
  rw [← encard_union_add_encard_inter]; exact le_self_add

-- TEST: anonymous functions
theorem TEST_encard_insert_of_not_mem {a : α} (has : a ∉ s) : (insert a s).encard = s.encard + 1 := by
  rw [← union_singleton, encard_union_eq (by simpa), encard_singleton]

-- TEST: rw; apply; intro; exact
theorem encard_le_encard_of_injOn (hf : MapsTo f s t) (f_inj : InjOn f s) :
    s.encard ≤ t.encard := by
  rw [← f_inj.encard_image]; apply encard_le_card; rintro _ ⟨x, hx, rfl⟩; exact hf hx

-- TODO: use this code to create proper testing for our parser
-- (https://github.com/leanprover/lean4/blob/bfb02be28168d05ae362d6d9a135ec93820ca1cb/src/Lean/Elab/InfoTrees.lean#L20)

-- elab "aliasC " x:ident " ← " ys:ident* : command =>
--   for y in ys do
--     Lean.logInfo y

-- elab "#explode " stx:term : command => Command.runTermElabM fun _ => do
--   let (heading, e) ← try
--     -- Adapted from `#check` implementation
--     let theoremName : Name ← realizeGlobalConstNoOverloadWithInfo stx
--     addCompletionInfo <| .id stx theoremName (danglingDot := false) {} none
--     let decl ← getConstInfo theoremName
--     let c : Expr := .const theoremName (decl.levelParams.map mkLevelParam)
--     pure (m!"{MessageData.ofConst c} : {decl.type}", decl.value!)
--   catch _ =>
--     let e ← Term.elabTerm stx none
--     Term.synthesizeSyntheticMVarsNoPostponing
--     let e ← Term.levelMVarToParam (← instantiateMVars e)
--     pure (m!"{e} : {← Meta.inferType e}", e)
--   unless e.isSyntheticSorry do
--     let entries ← explode e
--     let fitchTable : MessageData ← entriesToMessageData entries
--     logInfo <|← addMessageContext m!"{heading}\n\n{fitchTable}\n"


/--
info: lambda : True → True

0│   │ a  ├ True
1│0,0│ ∀I │ True → True
-/
-- #guard_msgs in #explode lambda
