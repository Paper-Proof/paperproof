import { PositionStartStop } from "types";
import { AnyTheoremSignature } from "./LeanProofTree";

export interface GoalNode {
  text: string;
  name: string;
  id: string;
}

export interface HypNode {
  // TODO I think hyps always have .text and .name?
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
export interface Table {
  tabledHyps: TabledHyp[];
  tabledTactics: TabledTactic[];
  currentRow: number;
  row1Hyps?: HypNode[];
}

export interface HypLayer {
  tacticId: string,
  hypNodes: HypNode[]
}

export interface Box {
  id: string;
  parentId: string | null | "haveBox" | "byBox";
  /**
   * **Raw information about what hypotheses and goals are in this box.**  
   * 
   * [inserted in `converter.ts`].  
   */
  goalNodes: GoalNode[];
  /**
   * **Raw information about what hypotheses and goals are in this box.**  
   * 
   * [inserted in `converter.ts`].  
   */
  hypLayers: HypLayer[];
  /**
   * **Derived prop (from `hypLayers` and `goalNodes`).**  
   * Tells us exactly where hypotheses should be located in the UI to make it pretty.  
   *
   * [inserted in `hypsToTables.ts`].  
   */
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
  byBoxIds: string[];
  position: PositionStartStop;
  theorems: AnyTheoremSignature[];
}

export interface ConvertedProofTree {
  boxes: Box[];
  tactics: Tactic[];
  equivalentIds: { [key: string]: string[] };
}
