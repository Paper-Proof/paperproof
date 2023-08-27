export type LeanHypothesis = {
  value: null | string;
  username: string;
  type: string;
  id: string;
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
