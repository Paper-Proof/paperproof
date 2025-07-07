import Lean

open Lean Server RequestM

namespace Paperproof.Services

-- TODO we should move this to another file, read on this (https://leanprover.github.io/functional_programming_in_lean/hello-world/starting-a-project.html)
def checkIfUserIsStillTyping (snap : Snapshots.Snapshot) (hoverPos : Lsp.Position) : RequestM Unit := do

  -- old: snap.beginPos
  if let some beginPosition := snap.stx.getPos? then
    let doc ← readDoc
    let text := doc.meta.text
    let snapBegins := text.utf8PosToLspPos beginPosition

    -- We won't get error messages for this,
    -- but if we have the following arrangement, then there is some syntax error:
    --
    --   snapBegins: (101, 0)
    --   hoverPos: (93, 4)
    --
    --    hover            snapBegins
    -- ─────┼──────────────────┼───────
    --      93                101
    let isSyntaxError := hoverPos.line < snapBegins.line

    if isSyntaxError then
      throwThe RequestError ⟨.invalidParams, "stillTyping"⟩

    for (msg : Message) in MessageLog.toList snap.msgLog do
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

end Paperproof.Services
