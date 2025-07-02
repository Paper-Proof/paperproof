import Lean

inductive State
  | start
  | tacticStringWillOccurSoon  
  | tacticStringStarted

def getClosestRw (text: Lean.FileMap) (hoverPos: String.Pos) : Id String := do
  let mut currentPosition : String.Pos := hoverPos
  let text : String := Lean.FileMap.source text
  let mut state : State := State.start
  let mut rwList : List Char := []

  while currentPosition != 0 do
    currentPosition := String.prev text currentPosition
    let currentChar := text.get currentPosition
    
    match state with
    | State.start => 
      if currentChar.toString == "[" then
        state := State.tacticStringWillOccurSoon
    | State.tacticStringWillOccurSoon => 
      if !currentChar.isWhitespace && !currentChar.isDigit then
        state := State.tacticStringStarted
        rwList := currentChar :: rwList
    | State.tacticStringStarted => 
      if !currentChar.isWhitespace then
        rwList := currentChar :: rwList
      else
        break

  return String.mk rwList
