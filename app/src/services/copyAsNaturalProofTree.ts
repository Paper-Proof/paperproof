import { ConvertedProofTree, Box, Tactic, NaturalHyp, NaturalStep, NaturalBox, NaturalProofTree } from "types";
import getHypById from "./getHypById";

const dependsOnNames = (proofTree: ConvertedProofTree, tactic: Tactic): string[] => {
  const parentIds = tactic.hypArrows.map(a => a.fromId);
  const usedIds = tactic.dependsOnIds.filter(id => getHypById(proofTree, id)?.isProof === "proof");
  const names = [...parentIds, ...usedIds].map(id => getHypById(proofTree, id)?.name).filter((n): n is string => !!n);
  return [...new Set(names)];
};

const deltaForBox = (box: Box, tactic: Tactic): NaturalHyp[] => {
  const layer = box.hypLayers.find(hl => hl.tacticId === tactic.id);
  return (layer?.hypNodes ?? []).map(h => ({ name: h.name || "", type: h.text || "" }));
};

const assignTacticsToBoxes = (proofTree: ConvertedProofTree): Map<string, Tactic[]> => {
  const goalToBox = new Map<string, string>();
  proofTree.boxes.forEach(box => box.goalNodes.forEach(g => goalToBox.set(g.id, box.id)));

  const hypToBox = new Map<string, string>();
  proofTree.boxes.forEach(box =>
    box.hypLayers.forEach(hl => hl.hypNodes.forEach(h => hypToBox.set(h.id, box.id)))
  );

  const tacticsByBox = new Map<string, Tactic[]>();
  proofTree.boxes.forEach(box => tacticsByBox.set(box.id, []));

  let lastBoxId: string | null = null;

  proofTree.tactics
    .filter(t => t.text !== "init")
    .sort((a, b) => parseInt(a.id) - parseInt(b.id))
    .forEach(tactic => {
      let boxId: string | null = null;
      if (tactic.goalArrows.length > 0) {
        boxId = goalToBox.get(tactic.goalArrows[0].fromId) || null;
      } else if (tactic.successGoalId) {
        boxId = goalToBox.get(tactic.successGoalId) || null;
      } else {
        const firstHypId = tactic.hypArrows.flatMap(a => a.toIds)[0];
        if (firstHypId) boxId = hypToBox.get(firstHypId) || null;
      }
      if (!boxId) boxId = lastBoxId;
      if (boxId && tacticsByBox.has(boxId)) {
        tacticsByBox.get(boxId)!.push(tactic);
        lastBoxId = boxId;
      }
    });

  return tacticsByBox;
};

const buildNaturalBox = (
  box: Box,
  proofTree: ConvertedProofTree,
  tacticsByBox: Map<string, Tactic[]>,
  entryHyps: NaturalHyp[]
): NaturalBox => {
  const goalNodeIds = new Set(box.goalNodes.map(g => g.id));
  const boxTactics = tacticsByBox.get(box.id) || [];
  const tactics: NaturalStep[] = [];

  for (const tactic of boxTactics) {
    const newHyps = deltaForBox(box, tactic);
    const dependsOn = dependsOnNames(proofTree, tactic);

    if (tactic.successGoalId && goalNodeIds.has(tactic.successGoalId)) {
      tactics.push({
        tactic: tactic.text,
        ...(dependsOn.length > 0 && { dependsOn }),
        ...(newHyps.length > 0 && { newHyps }),
        closed: true,
      });
      continue;
    }

    const subBoxIds = [...tactic.haveBoxIds, ...tactic.byBoxIds];
    if (subBoxIds.length > 0) {
      const haveBoxes = subBoxIds
        .map(id => proofTree.boxes.find(b => b.id === id))
        .filter((b): b is Box => !!b)
        .map(b => buildNaturalBox(b, proofTree, tacticsByBox, []));
      tactics.push({
        tactic: tactic.text,
        ...(dependsOn.length > 0 && { dependsOn }),
        ...(newHyps.length > 0 && { newHyps }),
        haveBoxes,
      });
      continue;
    }

    const childBoxes = tactic.goalArrows
      .map(a => proofTree.boxes.find(b => b.parentId === box.id && b.goalNodes[0]?.id === a.toId))
      .filter((b): b is Box => !!b);

    if (childBoxes.length > 1) {
      tactics.push({
        tactic: tactic.text,
        ...(dependsOn.length > 0 && { dependsOn }),
        ...(newHyps.length > 0 && { newHyps }),
        newSubgoals: childBoxes.map(cb =>
          buildNaturalBox(cb, proofTree, tacticsByBox, deltaForBox(cb, tactic))
        ),
      });
      continue;
    }

    const fromGoalText = tactic.goalArrows[0]?.fromId
      ? box.goalNodes.find(g => g.id === tactic.goalArrows[0].fromId)?.text
      : undefined;
    const toGoalText = tactic.goalArrows[0]?.toId
      ? box.goalNodes.find(g => g.id === tactic.goalArrows[0].toId)?.text
      : undefined;
    const goalChanged = toGoalText !== undefined && toGoalText !== fromGoalText;

    tactics.push({
      tactic: tactic.text,
      ...(dependsOn.length > 0 && { dependsOn }),
      ...(newHyps.length > 0 && { newHyps }),
      ...(goalChanged && { newGoal: toGoalText }),
    });
  }

  return {
    goal: box.goalNodes[0]?.text || "",
    newHyps: entryHyps,
    tactics,
  };
};

const copyAsNaturalProofTree = (proofTree: ConvertedProofTree): string => {
  const rootBox = proofTree.boxes.find(b => b.parentId === null);
  if (!rootBox) return "{}";

  const initTactic = proofTree.tactics.find(t => t.text === "init");
  const entryHyps = initTactic ? deltaForBox(rootBox, initTactic) : [];

  const tacticsByBox = assignTacticsToBoxes(proofTree);
  const rootNatural = buildNaturalBox(rootBox, proofTree, tacticsByBox, entryHyps);

  const natural: NaturalProofTree = { format: "unicode", ...rootNatural };

  return JSON.stringify(natural, null, 2);
};

export default copyAsNaturalProofTree;
