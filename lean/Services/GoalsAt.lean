import Lean

open Lean Elab

namespace Paperproof.Services

/-
  This is a DIRECT copypaste of Lean's `InfoTree.goalsAt?`, with one adjustment - we add the `!isClosingBracketInRewriteSequence` condition.
  ___Is it ok to edit this function?
     It's important to keep this function as close to the Lean's `InfoTree.goalsAt?` as possible, because users expect Paperproof to function similarly to InfoView.
  ___Why do we need `!isClosingBracketInRewriteSequence` condition?
     Without this condition, placing cursor after `rw [Set.mem_inter_iff, and_comm]|` results in Paperproof parsing `]` as a single tactic, which is useless - it's basically equivalent to `rw [rfl]`, and typically it doesn't show any interesting before/after changes.
     What the users do want to see upon placing their cursor on/after `]` is a full rewrite sequence.
-/
partial def goalsAt? (t : InfoTree) (text : FileMap) (hoverPos : String.Pos.Raw) : List GoalsAtResult :=
  let gs := t.collectNodesBottomUp fun ctx i cs gs => Id.run do
    if let Info.ofTacticInfo ti := i then
      if let (some pos, some tailPos) := (i.pos?, i.tailPos?) then
        let trailSize := i.stx.getTrailingSize
        -- dbg_trace trailSize
        -- show info at EOF even if strictly outside token + trail
        let atEOF := tailPos.byteIdx + trailSize == text.source.rawEndPos.byteIdx
        -- include at least one trailing character (see also `priority` below)
        if pos ≤ hoverPos ∧ (hoverPos.byteIdx < tailPos.byteIdx + max 1 trailSize || atEOF) then
          let isClosingBracketInRewriteSequence := ti.stx.getAtomVal == "]"
          if (gs.isEmpty || (hoverPos ≥ tailPos && gs.all (·.indented))) && !isClosingBracketInRewriteSequence then
            return [{
              ctxInfo := ctx
              tacticInfo := ti
              useAfter := hoverPos > pos && !cs.any (hasNestedTactic pos tailPos)
              -- consider every position unindented after an empty `by` to support "hanging" `by` uses
              -- indented :=
              indented := (text.toPosition pos).column > (text.toPosition hoverPos).column && !isEmptyBy ti.stx
              -- use goals just before cursor as fall-back only
              -- thus for `(by foo)`, placing the cursor after `foo` shows its state as long
              -- as there is no state on `)`
              priority := if hoverPos.byteIdx == tailPos.byteIdx + trailSize then 0 else 1
            }]
    return gs
  let maxPrio? := gs.map (·.priority) |>.max?
  gs.filter (some ·.priority == maxPrio?)
where
  hasNestedTactic (pos tailPos) : InfoTree → Bool
    | InfoTree.node i@(Info.ofTacticInfo _) cs => Id.run do
      if let `(by $_) := i.stx then
        return false  -- ignore term-nested proofs such as in `simp [show p by ...]`
      if let (some pos', some tailPos') := (i.pos?, i.tailPos?) then
        -- ignore preceding nested infos
        -- ignore nested infos of the same tactic, e.g. from expansion
        if tailPos' > hoverPos && (pos', tailPos') != (pos, tailPos) then
          return true
      cs.any (hasNestedTactic pos tailPos)
    | InfoTree.node (Info.ofMacroExpansionInfo _) cs =>
      cs.any (hasNestedTactic pos tailPos)
    | _ => false
  isEmptyBy (stx : Syntax) : Bool :=
    -- there are multiple `by` kinds with the same structure
    stx.getNumArgs == 2 && stx[0].isToken "by" && stx[1].getNumArgs == 1 && stx[1][0].isMissing

end Paperproof.Services

