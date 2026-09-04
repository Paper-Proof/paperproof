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
import { NaturalHyp, NaturalStep, NaturalBox, NaturalProofTree } from "./NaturalProofTree";
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
import { SnapshotPayload, SnapshotState } from "./Snapshot";

// SERVER REQUEST/RESPONSE
export interface ValidProofResponse {
  proofTree: LeanProofTree;
  goal: LeanInteractiveGoal | null;
  theorems?: TheoremSignature[];
}

export type ErroryProofResponse = { error: any; meta?: Record<string, any> };
export type ProofResponse = ValidProofResponse | ErroryProofResponse;

export interface Settings {
  isSingleTacticMode: boolean;
  isHiddenGoalNames : boolean;
  isGreenHypotheses : boolean;
  areHypsHighlighted: boolean;
  isFollowingCursor : boolean;
  isUnlimitedWidth  : boolean;
  fontSize          : number;
}

export interface LatexSettings {
  map         : Record<string, string>;
  isActive    : boolean;
  instructions: string;
  shortenWords: boolean;
}

export const DEFAULT_LATEX_SETTINGS: LatexSettings = {
  map         : {},
  isActive    : false,
  instructions: "",
  shortenWords: false,
};


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
  ArgumentInfo,
  NaturalHyp,
  NaturalStep,
  NaturalBox,
  NaturalProofTree,
  SnapshotPayload,
  SnapshotState
};

export { SNAPSHOT_VERSION } from "./Snapshot";
