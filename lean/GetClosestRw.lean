import Lean

def getClosestRw (text: Lean.FileMap) (hoverPos: String.Pos) : Id String := do
  let mut currentPosition : String.Pos := hoverPos
  let text : String := Lean.FileMap.source text
  let mut state : String := "start" 
  let mut rwList : List Char := []

  while currentPosition != 0 do
    currentPosition := String.prev text currentPosition
    let currentChar := text.get currentPosition
    if state == "start" && currentChar.toString == "[" then
      state := "tacticStringWillOccurSoon"
    else if state == "tacticStringWillOccurSoon" && !currentChar.isWhitespace && !currentChar.isDigit then
      state := "tacticStringStarted"
      rwList := currentChar :: rwList
    else if state == "tacticStringStarted" && !currentChar.isWhitespace then
      rwList := currentChar :: rwList
    else if state == "tacticStringStarted" && currentChar.isWhitespace then
      break

  return String.mk rwList
