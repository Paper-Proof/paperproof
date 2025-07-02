import { PositionStartStop } from "types";

export interface ArgumentInfo {
  name: string;
  type: string;
}

export type DeclarationType = "theorem" | "axiom" | "def";

export interface BaseTheoremSignature {
  name: string;
  instanceArgs: ArgumentInfo[];
  implicitArgs: ArgumentInfo[];
  explicitArgs: ArgumentInfo[];
  type: string;
  declarationType: DeclarationType;
}

export interface TheoremSignature extends BaseTheoremSignature {
  declarationType: "theorem";
  body: undefined;
}

export interface AxiomSignature extends BaseTheoremSignature {
  declarationType: "axiom";
  body: undefined;
}

export interface DefinitionSignature extends BaseTheoremSignature {
  declarationType: "def";
  body: string | undefined;
}

export type AnyTheoremSignature = TheoremSignature | AxiomSignature | DefinitionSignature;

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
  theorems: AnyTheoremSignature[];
};

export type LeanProofTree = LeanTactic[];
