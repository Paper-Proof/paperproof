import { ConvertedProofTree, LeanProofTree } from "types";
import getHypById from "./getHypById";

function getGoalById(convertedProofTree: ConvertedProofTree, goalId: string): string | null {
  for (const box of convertedProofTree.boxes) {
    const foundGoal = box.goalNodes.find(goalNode => goalNode.id === goalId);
    
    if (foundGoal) {
      return foundGoal.text;
    }
  }
  
  return null;
}

const logProofTreeForDebugging = (leanProofTree: LeanProofTree, convertedProofTree: ConvertedProofTree) => {
  // This is for feeding the proof structure to LLMs
  const copypaste = {
    tactics: convertedProofTree.tactics.map((tactic) => ({
      text: tactic.text,
      hypothesisChanges: tactic.hypArrows.map((a) => ({
        from: getHypById(convertedProofTree, a.fromId)?.text || null,
        to: a.toIds.map((id) => getHypById(convertedProofTree, id)?.text || null)
      })),
      goalChanges: tactic.goalArrows.map((a) => ({
        from: getGoalById(convertedProofTree, a.fromId),
        to: getGoalById(convertedProofTree, a.toId),
      })),
      closedSomeGoal: tactic.successGoalId ? getGoalById(convertedProofTree, tactic.successGoalId) : null
    }))
  }

  console.log({ leanProofTree, convertedProofTree, copypaste });
}

export default logProofTreeForDebugging;
