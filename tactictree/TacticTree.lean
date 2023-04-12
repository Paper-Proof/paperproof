import Lean
import Lean.Linter.Util
import Lean.Elab.Command

open Lean Lean.Meta Lean.Elab
open Lean Elab Command Linter

namespace TacticTree

register_option linter.tacticTree : Bool := {
  defValue := true
  descr := "enable the tactic tree linter"
}

partial def tacticTreeLinter : Linter := fun stx => do
  logLint linter.tacticTree stx m!"Fancy tactic tree linter {stx}"

initialize addLinter tacticTreeLinter