import { ConvertedProofTree } from "types";
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

interface HypothesisChange {
  from: string | null;
  to: (string | null)[];
}

interface GoalChange {
  from: string | null;
  to: string | null;
}

interface Tactic {
  text: string;
  hypothesisChanges: HypothesisChange[];
  goalChanges: GoalChange[];
  closedSomeGoal: string | null;
}

const copyProofStructureForLLM = (convertedProofTree: ConvertedProofTree) => {
  const tactics: Tactic[] = convertedProofTree.tactics.map((tactic) => ({
    text: tactic.text,
    hypothesisChanges: tactic.hypArrows.map((a) => {
      const fromHyp = getHypById(convertedProofTree, a.fromId)
      return {
        from: fromHyp ? `${fromHyp.name}: ${fromHyp.text}` : null,
        to: a.toIds
          .map((id) => getHypById(convertedProofTree, id))
          .filter((hyp) => !!hyp)
          .map((hyp) => `${hyp.name}: ${hyp.text}`)
      }
    }),
    goalChanges: tactic.goalArrows.map((a) => ({
      from: getGoalById(convertedProofTree, a.fromId),
      to: getGoalById(convertedProofTree, a.toId),
    })),
    closedSomeGoal: tactic.successGoalId ? getGoalById(convertedProofTree, tactic.successGoalId) : null
  }))

  const formatTactic = (tactic: Tactic, index: number): string => {
    let result = `TACTIC ${index}: \`${tactic.text}\``;

    const beforeGoal = tactic.goalChanges.length > 0 ? tactic.goalChanges[0].from : null;
    const afterGoal = tactic.goalChanges.length > 0 ? tactic.goalChanges[0].to : null;
    
    // Check if there are any actual changes to show
    const hasHypothesisChanges = tactic.hypothesisChanges.some(change => 
      change.from || change.to.some(hyp => hyp)
    );
    const hasGoalChanges = beforeGoal || afterGoal;

    if (hasHypothesisChanges || hasGoalChanges) {
      // Format before state
      result += '\n  ...';
      
      // Add hypotheses from before state
      tactic.hypothesisChanges.forEach(change => {
        if (change.from) {
          result += '\n  ' + change.from;
        }
      });
      
      if (beforeGoal) {
        result += '\n  ⊢ ' + beforeGoal;
      }
      
      // Add separator line
      result += '\n  ________________________________________________________________';
      
      // Format after state
      result += '\n  ...';
      
      // Add new hypotheses from changes
      tactic.hypothesisChanges.forEach(change => {
        change.to.forEach(hyp => {
          if (hyp) {
            result += '\n  ' + hyp;
          }
        });
      });
      
      if (afterGoal) {
        result += '\n  ⊢ ' + afterGoal;
      }
    }
    
    // Add closed goal if any
    if (tactic.closedSomeGoal) {
      result += `\n  CLOSED: ${tactic.closedSomeGoal}`;
    }
    
    result += '\n******************************************************************';
    
    return result;
  };

  const string = tactics.map(formatTactic).join('\n');
  return '******************************************************************\n' + string;
};

export default copyProofStructureForLLM;