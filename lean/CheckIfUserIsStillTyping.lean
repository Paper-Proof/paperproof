import Lean

open Lean Server RequestM

-- TODO we should move this to another file, read on this (https://leanprover.github.io/functional_programming_in_lean/hello-world/starting-a-project.html)
def checkIfUserIsStillTyping (snap : Snapshots.Snapshot) (hoverPos : Lsp.Position) : RequestM Unit := do
  let doc ← readDoc
  let text := doc.meta.text

  -- If we have this, then it's some syntax error:
  --   snap.beginPos: (101, 0)
  --   snap.endPos: (103, 0)
  --   hoverPos: (93, 4)
  --   => no error messages
  let isSyntaxError := hoverPos.line < (text.utf8PosToLspPos snap.beginPos).line

  if isSyntaxError then
    throwThe RequestError ⟨.invalidParams, "stillTyping"⟩

  let snapBegins : Lsp.Position := text.utf8PosToLspPos snap.beginPos
  for (msg : Message) in snap.msgLog.msgs do
    let messageHappened := text.leanPosToLspPos msg.pos
    if messageHappened.line >= snapBegins.line then
      -- Happens in these cases:
      -- .data equals "unknown tactic"
      -- .data equals "expected '(' or term"
      -- .data equals "unknown identifier 'm'"
      -- .data equals "tactic 'apply' failed, failed to unify..."
      let isError := match msg.severity with
        | MessageSeverity.error => true
        | _ => false
      -- Everything's fine, we'll get a nice InfoTree
      let isSorried := (← msg.data.toString).startsWith "unsolved goals"

      if isError && !isSorried then
        throwThe RequestError ⟨.invalidParams, "stillTyping"⟩
