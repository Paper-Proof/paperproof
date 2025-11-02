// Simplified user-friendly input types
export type UserHypothesis = {
  username?: string; // Optional, defaults to empty string
  type: string;
  id: string;
  isProof?: string; // Optional, defaults to "proof"
};

export type UserGoal = {
  type: string;
  id: string;
  username?: string; // Optional, defaults to "⊢"
  hyps: UserHypothesis[];
};

export type UserTactic = {
  tacticString: string;
  tacticDependsOn?: string[]; // Optional, defaults to []
  goalBefore: UserGoal;
  goalsAfter: UserGoal[];
  spawnedGoals?: UserGoal[]; // Optional, defaults to []
};

export type UserProofTree = UserTactic[];