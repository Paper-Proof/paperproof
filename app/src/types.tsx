import { App, TLShapeId } from "@tldraw/tldraw";

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
}

export interface Shared {
  app: App;
  uiConfig: UiConfig,
  arrowsToDraw: { fromId: string, toId: string }[],
  proofTree: Format,
  currentGoal: string
}