import { ConvertedProofTree, Box, HypNode, Tactic, NaturalHyp, NaturalStep, NaturalBox, NaturalProofTree } from "types";

// id → hyp name, searched across all boxes (ids are globally unique)
const nameOfHypId = (proofTree: ConvertedProofTree, id: string): string | undefined => {
  for (const box of proofTree.boxes) {
    for (const hl of box.hypLayers) {
      const hyp = hl.hypNodes.find(h => h.id === id);
      if (hyp?.name) return hyp.name;
    }
  }
  return undefined;
};

const resolveDepNames = (proofTree: ConvertedProofTree, ids: string[]): string[] =>
  ids.map(id => nameOfHypId(proofTree, id)).filter((n): n is string => !!n);

// For a hyp node produced by `tactic`, find the name of the hyp it descends from.
// We look at the tactic's hypArrows: the arrow whose `toIds` contains this hyp's id
// tells us its source. fromId === null means "appears from nothing" → no `from`.
const hypFrom = (
  proofTree: ConvertedProofTree,
  tactic: Tactic,
  hypId: string
): string | undefined => {
  const arrow = tactic.hypArrows.find(a => a.toIds.includes(hypId));
  if (!arrow || arrow.fromId === null) return undefined;
  return nameOfHypId(proofTree, arrow.fromId);
};

const mapHypNode = (proofTree: ConvertedProofTree, tactic: Tactic, h: HypNode): NaturalHyp => {
  const from = hypFrom(proofTree, tactic, h.id);
  return { name: h.name || "", type: h.text || "", ...(from && { from }) };
};

// The hyps a tactic introduces into a particular box (its hypLayer for that box).
const deltaForBox = (proofTree: ConvertedProofTree, box: Box, tactic: Tactic): NaturalHyp[] => {
  const layer = box.hypLayers.find(hl => hl.tacticId === tactic.id);
  if (!layer) return [];
  return layer.hypNodes.map(h => mapHypNode(proofTree, tactic, h));
};

// Assign each tactic to the box it operates in.
//   - goalArrows present  → box containing goalArrows[0].fromId
//   - successGoalId set   → box containing that goal id
//   - hypArrows present   → box containing the first hyp id  (covers `have` tactics)
//   - none of the above   → same box as the previous tactic  (covers rewrites at hyps)
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
  entryHyps: NaturalHyp[] // this box's own delta (computed by the caller from the parent tactic)
): NaturalBox => {
  const goalNodeIds = new Set(box.goalNodes.map(g => g.id));
  const boxTactics = tacticsByBox.get(box.id) || [];
  const tactics: NaturalStep[] = [];

  for (const tactic of boxTactics) {
    const newHyps = deltaForBox(proofTree, box, tactic);
    const dependsOn = resolveDepNames(proofTree, tactic.dependsOnIds);

    // Closing tactic
    if (tactic.successGoalId && goalNodeIds.has(tactic.successGoalId)) {
      tactics.push({
        tactic: tactic.text,
        ...(dependsOn.length > 0 && { dependsOn }),
        ...(newHyps.length > 0 && { newHyps }),
        closed: true,
      });
      continue;
    }

    // Have / by sub-proofs
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

    // Branching: multiple child boxes, each carrying only its own entry delta
    const childBoxes = tactic.goalArrows
      .map(a => proofTree.boxes.find(b => b.parentId === box.id && b.goalNodes[0]?.id === a.toId))
      .filter((b): b is Box => !!b);

    if (childBoxes.length > 1) {
      tactics.push({
        tactic: tactic.text,
        ...(dependsOn.length > 0 && { dependsOn }),
        ...(newHyps.length > 0 && { newHyps }),
        newSubgoals: childBoxes.map(cb =>
          buildNaturalBox(cb, proofTree, tacticsByBox, deltaForBox(proofTree, cb, tactic))
        ),
      });
      continue;
    }

    // Regular step: goal may change within the same box
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

  // Root's own hyps are introduced by the `init` tactic (all `from: null` → omitted).
  const initTactic = proofTree.tactics.find(t => t.text === "init");
  const entryHyps = initTactic ? deltaForBox(proofTree, rootBox, initTactic) : [];

  const tacticsByBox = assignTacticsToBoxes(proofTree);
  const rootNatural = buildNaturalBox(rootBox, proofTree, tacticsByBox, entryHyps);

  // Lean output is unicode; emit a complete NaturalProofTree (format is root-only).
  const natural: NaturalProofTree = { format: "unicode", ...rootNatural };

  return JSON.stringify(natural, null, 2);
};

export default copyAsNaturalProofTree;
