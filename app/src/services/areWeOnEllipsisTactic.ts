import { ConvertedProofTree, Highlights } from "types";
import getTacticByGoalId from "./getTacticByGoalId";

const areWeOnEllipsisTactic = (proofTree: ConvertedProofTree, highlights: Highlights) => {
   if (highlights) {
    const goalId = highlights.goalId;
    const tactic = getTacticByGoalId(proofTree, goalId);
    return !tactic || tactic.text.includes("sorry");
  }
  return false
}

export default areWeOnEllipsisTactic;
