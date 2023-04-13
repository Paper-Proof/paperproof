import Lean
import Lean.Linter.Util
import Lean.Elab.Command
import PaperProof

open Lean Lean.Meta Lean.Elab
open Lean Elab Command Linter
open Lean Widget

namespace TacticTree

register_option linter.tacticTree : Bool := {
  defValue := true
  descr := "enable the tactic tree linter"
}

def ppExpr' := Elab.Command.liftCoreM ∘ Lean.Meta.MetaM.run' ∘ ppExpr

partial def tacticTreeLinter : Linter := fun stx => do
  if let `(theorem $i:ident : $_ := $_) := stx then
    let trees ← getInfoTrees 
    let tree := trees[0]!
    let (_, state ) ← (parseTacticProof none none tree).run ⟨ .empty, [], [] ⟩

    let env ← getEnv 
    let type ← ppExpr' (env.find? i.getId).get!.type
    let state := {state with types := state.types.insert "top level" s!"{type}"}

    let fragments := findTree "top level" state
    logInfoAt i m!"{fragments.toJson}"

initialize addLinter tacticTreeLinter

end TacticTree

theorem th : ∀ {a b : Prop}, a ∧ b → b ∧ a := by
  intro a b h
  exact ⟨ h.right, h.left ⟩
