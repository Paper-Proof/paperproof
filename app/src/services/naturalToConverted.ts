import { ConvertedProofTree, Box, Tactic, HypNode, NaturalHyp, NaturalBox, fakePosition } from "types";
import addParents from "./addParents";

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

  const registerHypLayer = (
    box: Box,
    scope: Map<string, string>,
    tactic: Tactic,
    nhyps: NaturalHyp[]
  ) => {
    if (nhyps.length === 0) return;

    const hypNodes: HypNode[] = [];
    for (const h of nhyps) {
      const id = newNodeId();
      hypNodes.push({ text: h.type, name: h.name, id, isProof: "proof" });
      scope.set(h.name, id);
    }

    tactic.hypArrows.push({ fromId: null, toIds: hypNodes.map((h) => h.id), shardId: String(tactic.hypArrows.length) });
    box.hypLayers.push({ tacticId: tactic.id, hypNodes });
  };

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
          const childBox = walkBox(sg, box.id, scope, { tactic });
          tactic.goalArrows.push({ fromId: currentGoalId, toId: childBox.goalNodes[0].id });
        }
      } else if (step.newGoal) {
        const nextGoalId = newNodeId();
        box.goalNodes.push({ text: step.newGoal, name: "", id: nextGoalId });
        tactic.goalArrows.push({ fromId: currentGoalId, toId: nextGoalId });
        currentGoalId = nextGoalId;
      }
    }

    return box;
  };

  walkBox(root, null, new Map());

  return addParents({ boxes, tactics, equivalentIds: {} });
};

export default naturalToConverted;
