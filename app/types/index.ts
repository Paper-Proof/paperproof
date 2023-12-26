import { LeanHypothesis, LeanGoal, LeanTactic, LeanTacticApp, LeanHaveDecl, LeanProofTree } from './LeanProofTree';
import { LeanInteractiveHyp, LeanInteractiveGoal } from './LeanInteractiveGoal';
import { GoalNode, HypNode, Box, Tactic, ConvertedProofTree, TabledHyp, TabledTactic, TabledCell, Table, DataRow } from './ConvertedProofTree';

// SERVER REQUEST/RESPONSE
export interface ValidProofResponse {
  proofTree: LeanProofTree;
  goal: LeanInteractiveGoal | null;
}

export type ProofResponse = ValidProofResponse | { error: any };

export interface PaperProofWindow extends Window {
  initialInfo: ProofResponse | null;
  isBrightTheme: boolean;
}

// These are our /new types
type Highlights = HighlightsBody | null;
interface HighlightsBody {
  goalId: string;
  hypIds: string[];
}

interface Point {
  x: number;
  y: number;
}
interface Arrow {
  from: Point;
  to: Point;
}

export {
  LeanHypothesis, LeanGoal, LeanTactic, LeanTacticApp, LeanHaveDecl, LeanProofTree,

  LeanInteractiveHyp, LeanInteractiveGoal,

  GoalNode, HypNode, Box, Tactic, ConvertedProofTree,

  Highlights,
  TabledHyp, TabledTactic, TabledCell, Table, DataRow,
  Point, Arrow
};

