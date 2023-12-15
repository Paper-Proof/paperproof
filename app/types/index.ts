import { LeanHypothesis, LeanGoal, LeanTactic, LeanTacticApp, LeanHaveDecl, LeanProofTree } from './LeanProofTree';
import { LeanInteractiveHyp, LeanInteractiveGoal } from './LeanInteractiveGoal';
import { GoalNode, HypNode, HypLayer, Box, Tactic, ConvertedProofTree } from './ConvertedProofTree';
import { UIConfig, UIShared, UIHypTree, UIElement, UIIdElement, UINode, UINodeLayer } from './UI';

// SERVER REQUEST/RESPONSE
export interface ProofState {
  proofTree: LeanProofTree;
  goal: LeanInteractiveGoal | null;
}

export type ProofResponse = ProofState | { error: any } | null;

export interface PaperProofWindow extends Window {
  initialInfo: any | null;
  isBrightTheme: boolean;
}

// These are our /new types
type Highlights = HighlightsBody | null;
interface HighlightsBody {
  goalId: string;
  hypIds: string[];
}

interface TabledHyp {
  type: "hypothesis";
  hypNode: HypNode;
  columnFrom: number;
  columnTo: number;
  row: number;
}
interface TabledTactic {
  type: "tactic";
  tactic: Tactic;
  columnFrom: number;
  columnTo: number;
  row: number;
}
type TabledCell = TabledHyp | TabledTactic;
interface DataRow {
  hypNodes: HypNode[];
  width: number;
}
interface Table {
  tabledHyps: TabledHyp[];
  tabledTactics: TabledTactic[];
  currentRow: number;
  dataRow?: DataRow;
}

export {
  LeanHypothesis, LeanGoal, LeanTactic, LeanTacticApp, LeanHaveDecl, LeanProofTree,
  LeanInteractiveHyp, LeanInteractiveGoal,
  GoalNode, HypNode, Box, Tactic, HypLayer, ConvertedProofTree,
  UIConfig, UIShared, UIHypTree, UIElement, UIIdElement, UINode, UINodeLayer,

  Highlights,
  TabledHyp, TabledTactic, TabledCell, Table, DataRow
};

