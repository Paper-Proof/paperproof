import { PositionStartStop } from "types";

export interface ArgumentInfo {
  name: string;
  type: string;
}

export interface TheoremSignature {
  name: string;
  instanceArgs: ArgumentInfo[];
  implicitArgs: ArgumentInfo[];
  explicitArgs: ArgumentInfo[];
  type: string;
}

export type LeanHypothesis = {
  value: null | string;
  username: string;
  type: string;
  id: string;
  isProof: string;
};

export type LeanGoal = {
  username: string;
  type: string;
  id: string;
  hyps: LeanHypothesis[];
};

export type LeanTactic = {
  tacticString: string;
  tacticDependsOn: string[];
  goalBefore: LeanGoal;
  goalsAfter: LeanGoal[];
  spawnedGoals: LeanGoal[];
  position: PositionStartStop;
  theorems: TheoremSignature[];
};

export type LeanProofTree = LeanTactic[];
