import { PositionStartStop } from "types";

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
};

export type LeanProofTree = LeanTactic[];
