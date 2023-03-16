import Lean
open Lean Widget

@[widget]
def ppWidget: UserWidgetDefinition := {
  name := "Paper proof"
  javascript:= include_str "widget" / "dist" / "paperProof.js"
}

-- Check widget wiring
#widget ppWidget .null