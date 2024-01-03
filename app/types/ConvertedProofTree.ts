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
  isProof: string;
}

export interface TabledHyp {
  type: "hypothesis";
  hypNode: HypNode;
  columnFrom: number;
  columnTo: number;
  row: number;
}
export interface TabledTactic {
  type: "tactic";
  tactic: Tactic;
  columnFrom: number;
  columnTo: number;
  row: number;
  arrowFrom: string | null;
  shardId: string;
}
export type TabledCell = TabledHyp | TabledTactic;
export interface DataRow {
  hypNodes: HypNode[];
  width: number;
}
export interface Table {
  tabledHyps: TabledHyp[];
  tabledTactics: TabledTactic[];
  currentRow: number;
  dataRow?: DataRow;
}

export interface HypLayer {
  tacticId: string,
  hypNodes: HypNode[]
}

export interface Box {
  id: string;
  parentId: string | null | "haveBox";
  goalNodes: GoalNode[];
  hypLayers: HypLayer[];
  hypTables: Table[];
}

export interface Tactic {
  id: string;
  text: string;
  dependsOnIds: string[];
  goalArrows: { fromId: string; toId: string }[];
  hypArrows: { fromId: string | null; toIds: string[]; shardId: string }[];
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
