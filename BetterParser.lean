import Lean.Data.Json

open Lean

structure TacticApplication where
  tacticName : String
  goalsBefore : List String
  goalsAfter : List String
  tacticDependsOn : List String
  deriving Inhabited, ToJson

def parse (infoTree : InfoTree) : List TacticApplication :=
  [{
    tacticName := "ext x",
    goalsBefore := ["s ∩ t = t ∩ s"],
    goalsAfter := ["x ∈ s ∩ t ↔ x ∈ t ∩ s"],
    tacticDependsOn := []
    }]