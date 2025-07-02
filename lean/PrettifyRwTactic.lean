import Lean
import Lean.Meta.Basic
import Lean.Elab.Tactic

import GetTacticSubstring

open Lean Elab Meta Server RequestM

namespace Paperproof

inductive State
  | start
  | tacticStringWillOccurSoon  
  | tacticStringStarted

/--
  EXAMPLE
  `rw_mod_cast [Set.mem_inter_iff, and_com|m]` //=> `"rw_mod_cast"`
  `nth_rw 2 [Na|t.add_comm]` //=> `"nth_rw"`
-/
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

/--
  EXAMPLE
  `prettifyRwRule "Set.mem_inter_iff, "` //=> `"Set.mem_inter_iff"`
-/
def prettifyRwRule (tacticString : String) :=
  (tacticString.splitOn ",").head!.trim

def isTacticRwRule (tacticInfo: TacticInfo) : Bool :=
  let string : String := tacticInfo.stx.formatStx.pretty
  string.startsWith "[(Tactic.rwRule"

def prettifyRwTactic (tacticInfo : TacticInfo) (text : FileMap) (hoverPos : String.Pos) : RequestM String := do
  if (isTacticRwRule tacticInfo) then
    let .some tacticSubstring := getTacticSubstring tacticInfo | return ""
    let closestRwTacticName := getClosestRw text hoverPos
    
    let rwRule := (tacticSubstring.toString.splitOn ",").head!.trim
    pure s!"{closestRwTacticName} [{rwRule}]"
  else
    pure ""
