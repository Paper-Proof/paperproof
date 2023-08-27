import { LeanHypothesis, LeanGoal, LeanTactic, LeanTacticApp, LeanHaveDecl, LeanProofTree } from './LeanProofTree';
import { LeanInteractiveHyp, LeanInteractiveGoal } from './LeanInteractiveGoal';
import { GoalNode, HypNode, HypLayer, Window, Tactic, ConvertedProofTree } from './ConvertedProofTree';
import { UIConfig, UIShared, UIHypTree, UIElement, UIIdElement, UINode, UINodeLayer } from './UI';

// SERVER REQUEST/RESPONSE
export interface ProofState {
  proofTree: LeanProofTree;
  goal: LeanInteractiveGoal | null;
}

export type ProofResponse = ProofState | { error: any } | null;

export interface PaperProofWindow extends Window {
  initialInfo: any | null;
}

export {
  LeanHypothesis, LeanGoal, LeanTactic, LeanTacticApp, LeanHaveDecl, LeanProofTree,
  LeanInteractiveHyp, LeanInteractiveGoal,
  GoalNode, HypNode, Window, Tactic, HypLayer, ConvertedProofTree,
  UIConfig, UIShared, UIHypTree, UIElement, UIIdElement, UINode, UINodeLayer
};
