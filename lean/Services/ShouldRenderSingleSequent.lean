import Lean

open Lean Elab Server

namespace Paperproof.Services

def shouldRenderSingleSequent (tacticInfo : TacticInfo) (text : FileMap) (hoverPos : String.Pos) : RequestM Bool := do
  let .some tacticSubstring := tacticInfo.stx.getSubstring? | throwThe RequestError ⟨.invalidParams, "couldntFindTacticSubstring"⟩

  let file : String := Lean.FileMap.source text     
  let charBefore := file.get (String.prev file hoverPos)
  let charAfter  := file.get hoverPos
  let atEOF      := file.atEnd hoverPos
  let isNotOnTactic := charBefore.isWhitespace && (charAfter.isWhitespace || atEOF)

  let isBy := tacticSubstring.toString.trim == "by"
  return isNotOnTactic || isBy
