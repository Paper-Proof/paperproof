import { Editor, TLShapeId } from "@tldraw/tldraw";

// TLDRAW
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



// ConvertedProofTree
export interface GoalNode {
  text: string;
  name: string;
  id: string;
}

export interface HypNode {
  text: string;
  name: string | null;
  id: string;
  haveWindowId?: number;
}

export type HypLayer = HypNode[];

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
  initialGoal: GoalNode;
}


// InteractiveGoal
export interface InteractiveHyp {
  // `fvarIds` and `names` are always of the same length
  fvarIds: string[];
  names: string[];
  // type with all the stuff that lets us hover over it
  type: object;
}

export interface InteractiveGoal {
  ctx: object;
  goalPrefix: string;
  hyps: InteractiveHyp[];
  mvarId: string;
  // type with all the stuff that lets us hover over it
  type: object;
  userName: string;
}


// JUST USEFUL CODE
export interface ProofState {
  proofTree: Format;
  goal: InteractiveGoal | null;
}

export type ProofResponse = ProofState | { error: any } | null;

export interface PaperProofWindow extends Window {
  sessionId: string | null;
  initialInfo: any | null;
}

export interface Shared {
  editor: Editor;
  uiConfig: UiConfig;
  proofTree: Format;
  inBetweenMargin: number;
  framePadding: number;
}
