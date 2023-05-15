import Lean.Data.Json
import BetterParser

open Lean

structure SimpleEdge where
  tacticString : String
  fromNode : String
  toNode : String
  hypName : Option String
  deriving Inhabited, ToJson

inductive Edge :=
  | simple (e : SimpleEdge)
  | haveDecl (name : String) (edges : List Edge)
  deriving Inhabited

partial def toJsonEdge : Edge -> Json
  | Edge.simple e => toJson e
  | Edge.haveDecl name edges => Json.mkObj [
      ("name", toJson name),
      ("edges", Json.arr $ edges.toArray.map toJsonEdge)]

-- instance ToJson for SimpleEdge
instance : ToJson Edge where
  toJson := toJsonEdge

partial def findEdges (steps : List ProofStep) : List Edge :=
  steps.bind (fun s => Id.run do
    match s with
    | ProofStep.tacticApp t => 
      let [goalBefore] := t.goalsBefore
        | panic! "Expected one goal before"
      if t.goalsAfter.isEmpty then
        return [Edge.simple {
          tacticString := t.tacticString,
          fromNode := goalBefore.type,
          toNode := "⊢",
          hypName := none
        }]
      return t.goalsAfter.bind fun goalAfter =>
        let betweenGoals : List Edge := if goalBefore.type != goalAfter.type then
        [Edge.simple {
          tacticString := t.tacticString,
          fromNode := goalBefore.type,
          toNode := goalAfter.type,
          hypName := none
        }] else []
        let hyps := [goalBefore.hyps, goalAfter.hyps].join.map (·.username) |>.eraseDups
        let betweenHyps := hyps.filterMap fun hyp =>
          let hypBefore? := goalBefore.hyps.find? fun h => h.username == hyp
          let hypAfter? := goalAfter.hyps.find? fun h => h.username == hyp
          match hypBefore?, hypAfter? with
          | some hypBefore, some hypAfter =>
              if hypBefore.type != hypAfter.type then
                some $ .simple {
                  tacticString := t.tacticString,
                  fromNode := hypBefore.type,
                  toNode := hypAfter.type,
                  hypName := some hyp
                }
              else none
          | none, some hypAfter =>
                some $ .simple {
                  tacticString := t.tacticString,
                  fromNode := "⊢",
                  toNode := hypAfter.type,
                  hypName := some hyp
                }     
          | _, _ => none
        [betweenGoals, betweenHyps].bind id
    | ProofStep.haveDecl name steps => [Edge.haveDecl name $ findEdges steps]
  )
