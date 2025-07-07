import { Position, PositionStartStop } from "types";

const isCursorWithinTactic = (cursor: Position, tactic: PositionStartStop): boolean => {
  // If tactic spans many lines, it just means it's the last tactic in this proof, and Lean thinks empty lines below belong to this tactic
  const tacticSpansManyLines = tactic.stop.line - tactic.start.line > 1;
  const stopLine = tacticSpansManyLines ? tactic.start.line + 1 : tactic.stop.line;
  const stopCharacter = tacticSpansManyLines ? 0 : tactic.stop.character;
  return (
    cursor.line > tactic.start.line || 
    (cursor.line === tactic.start.line && cursor.character >= tactic.start.character)
  )
  &&
  (
    cursor.line < stopLine || 
    (cursor.line === stopLine && cursor.character < stopCharacter)
  );
};

export default isCursorWithinTactic;
