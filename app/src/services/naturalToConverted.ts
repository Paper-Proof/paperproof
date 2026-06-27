import { ConvertedProofTree, Box, Tactic, HypNode, NaturalHyp, NaturalBox, fakePosition } from "types";

// This is the inverse of `copyAsNaturalProofTree`. Because the NaturalProofTree format
// already contains the hypothesis arrows explicitly (`from`) and the box structure
// (nesting), we can build a `ConvertedProofTree` directly — no diffing, no
// id-aliasing. That's why we skip `converter()` entirely: its hard job is
// recovering exactly what we're handed.
const naturalToConverted = (root: NaturalBox): ConvertedProofTree => {
  const boxes: Box[] = [];
  const tactics: Tactic[] = [];

  let boxCounter = 1;    // root must be "1" (BoxEl special-cases it)
  let tacticCounter = 1;
  let nodeCounter = 1;
  const newBoxId = () => String(boxCounter++);
  const newTacticId = () => String(tacticCounter++);
  const newNodeId = () => `n${nodeCounter++}`;

  const makeTactic = (text: string): Tactic => {
    const t: Tactic = {
      id: newTacticId(),
      text,
      dependsOnIds: [],
      goalArrows: [],
      hypArrows: [],
      haveBoxIds: [],
      byBoxIds: [],
      position: { start: fakePosition, stop: fakePosition },
      theorems: [],
    };
    tactics.push(t);
    return t;
  };

  const resolveNames = (scope: Map<string, string>, names?: string[]): string[] =>
    (names ?? [])
      .map((n) => scope.get(n))
      .filter((id): id is string => !!id);

  // Build one hypLayer in `box` from `nhyps`, tagged with `tactic`.
  // Arrows are grouped by source WITHIN this layer (matching converter's behaviour),
  // but always get fresh shard ids — separate calls never merge.
  const registerHypLayer = (
    box: Box,
    scope: Map<string, string>,
    tactic: Tactic,
    nhyps: NaturalHyp[]
  ) => {
    if (nhyps.length === 0) return;

    const hypNodes: HypNode[] = [];
    const layerArrows = new Map<string | null, string[]>();

    for (const h of nhyps) {
      // Resolve `from` BEFORE binding this hyp's name, so a self-rewrite
      // ({name:"h1", from:"h1"}) points at the OLD h1, not itself.
      const fromId = h.from ? (scope.get(h.from) ?? null) : null;
      const id = newNodeId();
      hypNodes.push({ text: h.type, name: h.name, id, isProof: "proof" });

      const toIds = layerArrows.get(fromId) ?? [];
      toIds.push(id);
      layerArrows.set(fromId, toIds);

      scope.set(h.name, id);
    }

    for (const [fromId, toIds] of layerArrows) {
      tactic.hypArrows.push({ fromId, toIds, shardId: String(tactic.hypArrows.length) });
    }
    box.hypLayers.push({ tacticId: tactic.id, hypNodes });
  };

  // entry?: the tactic that introduces this box's `newHyps` (the branching tactic
  // for a subgoal). Root/have boxes have no entry tactic → we mint an "init" one.
  const walkBox = (
    nbox: NaturalBox,
    parentId: Box["parentId"],
    parentScope: Map<string, string>,
    entry?: { tactic: Tactic }
  ): Box => {
    const scope = new Map(parentScope);
    const goalId = newNodeId();

    const box: Box = {
      id: newBoxId(),
      parentId,
      goalNodes: [{ text: nbox.goal, name: "", id: goalId }],
      hypLayers: [],
      hypTables: [],
    };
    boxes.push(box);

    if (nbox.newHyps && nbox.newHyps.length > 0) {
      const entryTactic = entry?.tactic ?? makeTactic("init");
      registerHypLayer(box, scope, entryTactic, nbox.newHyps);
    }

    let currentGoalId = goalId;

    for (const step of nbox.tactics) {
      const tactic = makeTactic(step.tactic);
      tactic.dependsOnIds = resolveNames(scope, step.dependsOn);

      if (step.newHyps && step.newHyps.length > 0) {
        registerHypLayer(box, scope, tactic, step.newHyps);
      }

      if (step.closed) {
        tactic.successGoalId = currentGoalId;
      } else if (step.haveBoxes && step.haveBoxes.length > 0) {
        for (const hb of step.haveBoxes) {
          const childBox = walkBox(hb, "haveBox", scope);
          tactic.haveBoxIds.push(childBox.id);
        }
      } else if (step.newSubgoals && step.newSubgoals.length > 0) {
        for (const sg of step.newSubgoals) {
          // The branching tactic introduces each subgoal's entry hyps, so we pass
          // it as the entry tactic — its hypArrows accumulate across all branches.
          const childBox = walkBox(sg, box.id, scope, { tactic });
          tactic.goalArrows.push({ fromId: currentGoalId, toId: childBox.goalNodes[0].id });
        }
      } else if (step.newGoal) {
        const nextGoalId = newNodeId();
        box.goalNodes.push({ text: step.newGoal, name: "", id: nextGoalId });
        tactic.goalArrows.push({ fromId: currentGoalId, toId: nextGoalId });
        currentGoalId = nextGoalId;
      }
      // else: a hyp-only step — renders inside the hyp table, no goal arrow.
    }

    return box;
  };

  walkBox(root, null, new Map());

  return { boxes, tactics, equivalentIds: {} };
};

export default naturalToConverted;
