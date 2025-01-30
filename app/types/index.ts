import {
  LeanHypothesis,
  LeanGoal,
  LeanTactic,
  LeanProofTree,
} from "./LeanProofTree";
import { LeanInteractiveHyp, LeanInteractiveGoal } from "./LeanInteractiveGoal";
import {
  GoalNode,
  HypNode,
  Box,
  Tactic,
  ConvertedProofTree,
  TabledHyp,
  TabledTactic,
  TabledCell,
  Table,
  HypLayer
} from "./ConvertedProofTree";
import { ContextMenuType } from "./Mui";

// SERVER REQUEST/RESPONSE
export interface ValidProofResponse {
  // Version of the Lean RPC response. `undefined` is version 1. We use to issue
  // user messages to update lean library or refresh vscode to avoid maintaining
  // backwards compatibility between lean/app versions.
  version?: number;
  proofTree: LeanProofTree;
  goal: LeanInteractiveGoal | null;
}

export type ProofResponse = ValidProofResponse | { error: any };

export interface Settings {
  isCompactMode    : boolean;
  isCompactTactics : boolean;
  isReadonlyMode   : boolean;
  isHiddenGoalNames: boolean;
  isGreenHypotheses: boolean;
}

export interface PaperproofWindow extends Window {
  initialInfo: ProofResponse | null;
  initialSettings: Settings
}

export type PaperproofAcquireVsCodeApi = () => {
  postMessage: (message: {
    type: 'from_webview:update_settings';
    data: Settings;
  }) => void;
  getState: () => unknown;
  setState: (newState: unknown) => void;
};

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
  LeanHypothesis,
  LeanGoal,
  LeanTactic,
  LeanProofTree,
  LeanInteractiveHyp,
  LeanInteractiveGoal,
  // Uhh temporary. We should think about how to better name components (GoalNode, GoalNodeEl?) VS types (GoalNode, TypeGoalNode?).
  GoalNode as TypeGoalNode,
  HypNode,
  Box,
  Tactic,
  ConvertedProofTree,
  Highlights,
  TabledHyp,
  TabledTactic,
  TabledCell,
  Table,
  Point,
  Arrow,
  HypLayer,
  ContextMenuType
};
