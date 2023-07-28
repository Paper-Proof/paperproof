import { Editor as App, TLShapeId } from "@tldraw/tldraw";

export interface UiConfig {
  hideNulls: boolean
}

export interface HypTree {
  level: number;
  tactic: Element;
  nodes: { node: Element, tree?: HypTree }[];
}

export interface Element {
  size: [number, number];
  draw: (x: number, y: number, prefferedWidth?: number) => void;
}

export interface IdElement extends Element {
  id: TLShapeId;
}

export type Node = { text: string; id: string; name?: string; subNodes?: NodeLayer[] };

export type NodeLayer = Node[];

export interface GoalNode {
  name: string;
  text: string;
  id: string;
}

export interface HypNode {
  text: string;
  name: string | null;
  id: string;
  haveWindowId?: number;
}

export type HypLayer = HypNode[];

// Converter.js types
export interface Window {
  id: number;
  parentId: number | null;
  goalNodes: GoalNode[];
  hypNodes: HypLayer[];
}

export interface Tactic {
  id: string;
  text: string;
  dependsOnIds: string[];
  goalArrows: { fromId: string; toId: string }[];
  hypArrows: { fromId: string | null; toIds: string[] }[];
  // hmm
  isSuccess: boolean | string;
  successGoalId?: string;
  haveWindowId?: number
}

export interface Format {
  windows: Window[];
  tactics: Tactic[];
  equivalentIds: {[key: string]: string[]};
}

// What we share in tldraw code
export interface Shared {
  app: App;
  uiConfig: UiConfig;
  proofTree: Format;
  inBetweenMargin: number;
  framePadding: number;
}

// Focusing on the goal types
export interface InteractiveHyp {
  // `fvarIds` and `names` are always of the same length
  fvarIds: string[],
  names: string[],
  // type with all the stuff that lets us hover over it
  type: object
}

export interface InteractiveGoal {
  ctx: object;
  goalPrefix: string,
  hyps: InteractiveHyp[],
  mvarId: string,
  // type with all the stuff that lets us hover over it
  type: object,
  userName: string
}

export interface ProofState {
  statement: string;
  proofTree: Format;
  goal: InteractiveGoal;
}

export type ProofResponse = ProofState | { error: any } | null;

export interface PaperProofWindow extends Window {
  sessionId: string | null;
  initialInfo: any | null;
}
