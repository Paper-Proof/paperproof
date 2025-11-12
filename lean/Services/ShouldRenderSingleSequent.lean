import Lean

open Lean Elab Server

namespace Paperproof.Services

def shouldRenderSingleSequent (tacticInfo : TacticInfo) (text : FileMap) (hoverPos : String.Pos.Raw) : RequestM Bool := do
  let .some tacticSubstring := tacticInfo.stx.getSubstring? | throwThe RequestError ⟨.invalidParams, "couldntFindTacticSubstring"⟩

  let file : String := Lean.FileMap.source text
  let charBefore := hoverPos.prev file |>.get file
  let charAfter  := hoverPos.get file
  let atEOF      := hoverPos.atEnd file
  let isNotOnTactic := charBefore.isWhitespace && (charAfter.isWhitespace || atEOF)

  let isBy := tacticSubstring.toString.trim == "by"
  return isNotOnTactic || isBy
