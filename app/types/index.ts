import {
  LeanHypothesis,
  LeanGoal,
  LeanTactic,
  LeanProofTree,
  TheoremSignature,
  AxiomSignature,
  DefinitionSignature,
  AnyTheoremSignature,
  ArgumentInfo,
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
  theorems?: TheoremSignature[];
}

export type ErroryProofResponse = { error: any };
export type ProofResponse = ValidProofResponse | ErroryProofResponse;

export interface Settings {
  isSingleTacticMode: boolean;
  isCompactMode     : boolean;
  isCompactTactics  : boolean;
  isHiddenGoalNames : boolean;
  isGreenHypotheses : boolean;
  areHypsHighlighted: boolean;
}

export interface PaperproofWindow extends Window {
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

export interface Position {
  line: number;
  character: number;
}

export const fakePosition : Position = {
  line: -1,
  character: -1
}

export interface PositionStartStop {
  start: Position;
  stop: Position;
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
  ContextMenuType,
  TheoremSignature,
  AxiomSignature,
  DefinitionSignature,
  AnyTheoremSignature,
  ArgumentInfo
};
