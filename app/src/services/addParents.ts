import { ConvertedProofTree } from "types";
import getHypById from "./getHypById";

const addParents = (proofTree: ConvertedProofTree): ConvertedProofTree => {
  const useCounts = new Map<string, number>();
  proofTree.tactics.forEach((tactic) => new Set(tactic.dependsOnIds).forEach((id) => useCounts.set(id, (useCounts.get(id) ?? 0) + 1)));

  proofTree.tactics.forEach((tactic) => {
    const usedOnlyHere = [...new Set(tactic.dependsOnIds)].filter((id) =>
      useCounts.get(id) === 1 && getHypById(proofTree, id)?.isProof === "proof"
    );
    if (usedOnlyHere.length !== 1) return;
    tactic.hypArrows.forEach((hypArrow) => {
      if (hypArrow.fromId === null) hypArrow.fromId = usedOnlyHere[0];
    });
  });

  return proofTree;
};

export default addParents;
