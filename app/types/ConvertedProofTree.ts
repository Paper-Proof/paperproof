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
  isProof: boolean;
}

export type HypLayer = HypNode[];

export interface Box {
  id: string;
  parentId: string | null | "haveBox";
  goalNodes: GoalNode[];
  hypNodes: HypLayer[];
}

export interface Tactic {
  id: string;
  text: string;
  dependsOnIds: string[];
  goalArrows: { fromId: string; toId: string }[];
  hypArrows: { fromId: string | null; toIds: string[] }[];
  successGoalId?: string;
  // TODO: Those are actually `byBox`s which were used to create
  // parameters for this tactic. For example in
  // `have <p, q> := <by rfl, by trivial>`
  // there are 2 `byBox`s.
  haveBoxIds: string[];
}

export interface ConvertedProofTree {
  boxes: Box[];
  tactics: Tactic[];
  equivalentIds: { [key: string]: string[] };
}
