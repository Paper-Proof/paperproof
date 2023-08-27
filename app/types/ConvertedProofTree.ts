import { LeanInteractiveGoal } from 'types';

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
  equivalentIds: { [key: string]: string[] };
}
