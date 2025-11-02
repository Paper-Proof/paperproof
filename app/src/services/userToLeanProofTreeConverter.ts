import { UserProofTree, UserGoal, UserHypothesis, UserTactic } from "types/UserProofTree";
import { LeanProofTree, LeanGoal, LeanHypothesis, LeanTactic } from "types/LeanProofTree";
import { fakePosition } from "types";

const convertUserHypothesis = (userHyp: UserHypothesis): LeanHypothesis => ({
  value: null,
  username: userHyp.username || "",
  type: userHyp.type,
  id: userHyp.id,
  isProof: userHyp.isProof || "proof"
});

const convertUserGoal = (userGoal: UserGoal): LeanGoal => ({
  username: userGoal.username || "",
  type: userGoal.type,
  id: userGoal.id,
  hyps: userGoal.hyps.map(convertUserHypothesis)
});

const convertUserTactic = (userTactic: UserTactic): LeanTactic => ({
  tacticString: userTactic.tacticString,
  tacticDependsOn: userTactic.tacticDependsOn || [],
  goalBefore: convertUserGoal(userTactic.goalBefore),
  goalsAfter: userTactic.goalsAfter.map(convertUserGoal),
  spawnedGoals: (userTactic.spawnedGoals || []).map(convertUserGoal),
  position: { start: fakePosition, stop: fakePosition },
  theorems: []
});

export const convertUserProofTreeToLean = (userProofTree: UserProofTree): LeanProofTree => {
  return userProofTree.map(convertUserTactic);
};
