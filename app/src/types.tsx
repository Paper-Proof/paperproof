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
  text: string | null;
  name: string | null;
  id: string;
  haveWindowId?: number;
}

export type HypLayer = HypNode[];

export interface Window {
  id: string;
  parentId: string | null | "haveWindow";
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
  haveWindowId?: string
}

export interface ConvertedProofTree {
  windows: Window[];
  tactics: Tactic[];
  equivalentIds: {[key: string]: string[]};
  initialGoal: LeanGoal;
}
















// LeanProofTree

export type LeanHypothesis = {
  value: null | string;
  username: string;
  type: string;
  id: string;
};

// export interface HypNode {
//   text: string;
//   name: string | null;
//   id: string;
//   haveWindowId?: number;
// }

export type LeanGoal = {
  username: string;
  type: string;
  id: string;
  hyps: LeanHypothesis[];
};

export type LeanTactic = {
  tacticString: string;
  tacticDependsOn: string[];
  goalsBefore: LeanGoal[];
  goalsAfter: LeanGoal[];
};

export type LeanTacticApp = {
  tacticApp: {
    t: LeanTactic;
  }
};

export type LeanHaveDecl = {
  haveDecl: {
    t: LeanTactic;
    subSteps: LeanProofTree;
    initialGoal: string;
  }
};

export type LeanProofTree = (LeanTacticApp | LeanHaveDecl)[];











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
  proofTree: LeanProofTree;
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
  proofTree: ConvertedProofTree;
  inBetweenMargin: number;
  framePadding: number;
}
