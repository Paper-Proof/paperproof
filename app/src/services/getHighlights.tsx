import { ConvertedProofTree, Highlights, LeanInteractiveGoal } from "types";
import getDisplayedId from "src/services/getDisplayedId";

const getHighlights = (equivalentIds: ConvertedProofTree['equivalentIds'], currentGoal: LeanInteractiveGoal | null): Highlights => {
  if (!currentGoal) return null;

  const goalId = getDisplayedId(equivalentIds, currentGoal.mvarId);
  const hypIds = currentGoal.hyps
    .reduce<string[]>((acc, hyp) => [...acc, ...hyp.fvarIds], [])
    .map((inferiorHypId) => {
      const hypId = getDisplayedId(equivalentIds, inferiorHypId);
      return hypId;
    });
  return { goalId, hypIds };
};

export default getHighlights;
