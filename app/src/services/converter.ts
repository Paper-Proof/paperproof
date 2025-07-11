import { LeanProofTree, LeanHypothesis, LeanTactic, LeanGoal, ConvertedProofTree, Tactic, HypNode, Box, fakePosition } from "types";

let boxId: number;
let tacticId: number;

const newBoxId = () => {
  return String(boxId++);
};

const newTacticId = () => {
  return String(tacticId++);
};

// These are our weird situations:
//
// same id, same usernames, different type
// same id, different usernames, same type
// same id, different usernames, different type
// same id, same usernames, different type
//
// Notice how they all concern the situation where something important changed, but the id didn't!
// In such cases - let's trust Lean that the change is so miniscule it isn't worth the id update.
//
// IF we stumble upon the situation where this behaviour is undesirable - let's create a complex data structure that creates new fake ids; and keep track of them in a way that accounts for box parenthood relationships.
const weirdSituation = (
  pretty: ConvertedProofTree,
  hypAfter: LeanHypothesis
) => {
  console.warn(
    "Weird situation! Changing existingHypNode into hypAfter in-place:"
  );
  // We need a displayed id here [because, unusually enough, we're changing the already-drawn node]
  const hypAfterId = getDisplayedId(pretty, hypAfter.id);
  pretty.boxes.forEach((w) => {
    w.hypLayers.forEach((hypLayer) => {
      hypLayer.hypNodes.forEach((existingHypNode) => {
        if (existingHypNode.id === hypAfterId) {
          existingHypNode.name = hypAfter.username;
          existingHypNode.text = hypAfter.type;
        }
      });
    });
  });
};

const drawNewHypothesisLayer = (
  pretty: ConvertedProofTree,
  hypsBefore: LeanHypothesis[],
  hypsAfter: LeanHypothesis[]
): [HypNode[], Tactic["hypArrows"]] => {
  const prettyHypNodes: HypNode[] = [];
  const prettyHypArrows: Tactic["hypArrows"] = [];

  const hypsAfterMatched: LeanHypothesis[] = [];
  const hypsBeforeMatched: LeanHypothesis[] = [];

  // 1. Draw hypotheses that are clearly connected to a particular previous hypothesis
  hypsAfter.forEach((hypAfter) => {
    const hypBeforeById = hypsBefore.find((hyp) => hyp.id === hypAfter.id);
    const hypBeforeByName = hypsBefore.find(
      (hypBefore) =>
        hypBefore.username === hypAfter.username &&
        // Only match by username if that hypBefore wasn't already matched by id with someone else.
        // See github.com/antonkov/paper-proof/issues/10.
        !hypsAfter.find((h) => h.id === hypBefore.id && h.id !== hypAfter.id)
    );

    if (hypBeforeById) {
      hypsAfterMatched.push(hypAfter);
      hypsBeforeMatched.push(hypBeforeById);

      if (
        hypAfter.username === hypBeforeById.username &&
        hypAfter.type === hypBeforeById.type
      ) {
        // do nothing!
      } else if (
        hypAfter.username === hypBeforeById.username &&
        hypAfter.type !== hypBeforeById.type
      ) {
        weirdSituation(pretty, hypAfter);
      } else if (
        hypAfter.username !== hypBeforeById.username &&
        hypAfter.type === hypBeforeById.type
      ) {
        weirdSituation(pretty, hypAfter);
      } else if (
        hypAfter.username !== hypBeforeById.username &&
        hypAfter.type !== hypBeforeById.type
      ) {
        weirdSituation(pretty, hypAfter);
      }
    } else if (hypBeforeByName) {
      hypsAfterMatched.push(hypAfter);
      hypsBeforeMatched.push(hypBeforeByName);

      if (
        hypAfter.id === hypBeforeByName.id &&
        hypAfter.type === hypBeforeByName.type
      ) {
        // do nothing!
      } else if (
        hypAfter.id === hypBeforeByName.id &&
        hypAfter.type !== hypBeforeByName.type
      ) {
        weirdSituation(pretty, hypAfter);
      } else if (
        hypAfter.id !== hypBeforeByName.id &&
        hypAfter.type === hypBeforeByName.type
      ) {
        // don't create any new nodes or arrows, just add `hypAfter.id` to equivalentIds
        addToEquivalentIds(pretty, hypBeforeByName.id, hypAfter.id);
      } else if (
        hypAfter.id !== hypBeforeByName.id &&
        hypAfter.type !== hypBeforeByName.type
      ) {
        // draw a new node, draw an arrow
        prettyHypNodes.push({
          text: hypAfter.type,
          name: hypAfter.username,
          id: hypAfter.id,
          isProof: hypAfter.isProof,
        });

        prettyHypArrows.push({
          fromId: hypBeforeByName.id,
          toIds: [hypAfter.id],
          shardId: "temporary",
        });
      }
    }
  });

  // 2. Draw hypotheses that disappeared and appeared out of nowhere
  const hypsBeforeThatDisappeared = hypsBefore.filter(
    (hyp) => !hypsBeforeMatched.some((matchedHyp) => matchedHyp.id === hyp.id)
  );
  const hypsAfterThatAppeared = hypsAfter.filter(
    (hyp) => !hypsAfterMatched.some((matchedHyp) => matchedHyp.id === hyp.id)
  );

  // - if 0 hypotheses disappeared, and 0 hypotheses appeared, do nothing!
  if (
    hypsBeforeThatDisappeared.length === 0 &&
    hypsAfterThatAppeared.length === 0
  ) {
    // done :-)
  }
  // - if 0 hypotheses disappeared, and X hypotheses appeared, draw { null → id } arrows [many nulls!]
  else if (
    hypsBeforeThatDisappeared.length === 0 &&
    hypsAfterThatAppeared.length > 0
  ) {
    hypsAfterThatAppeared.forEach((hypAfter) => {
      prettyHypNodes.push({
        text: hypAfter.type,
        name: hypAfter.username,
        id: hypAfter.id,
        isProof: hypAfter.isProof,
      });
    });
    if (hypsAfterThatAppeared.length > 0) {
      prettyHypArrows.push({
        fromId: null,
        toIds: hypsAfterThatAppeared.map((hypAfter) => hypAfter.id),
        shardId: "temporary",
      });
    }
  }
  // - if X hypotheses disappeared, and 0 hypotheses appeared - don't draw anything
  else if (
    hypsBeforeThatDisappeared.length > 0 &&
    hypsAfterThatAppeared.length === 0
  ) {
    // Don't draw anything, this will be indicated by opacities
  }
  // - if X hypotheses disappeared, and X hypotheses appeared, draw { everything → everything } arrows
  else if (
    hypsBeforeThatDisappeared.length > 0 &&
    hypsAfterThatAppeared.length > 0
  ) {
    // The 2nd part of this `else if` doesn't ever happen as far as we're aware -
    // When we actually stumble upon a tactic that does that, we'll see how good our handling of this is.
    if (
      hypsBeforeThatDisappeared.length > 1 &&
      hypsAfterThatAppeared.length > 0
    ) {
      // TODO: add `if this.env === "development"` and uncomment this.
      // alert("FINALLY; We have stumbled upon the mysterious tactic that makes 2 hypotheses join into 1 hypothesis");
    }

    // `branchingHypBefore` is taken to be the 1st hyp, but we could have taken any hypothesis.
    // Theoretically, there is only ever 1 hypothesis here.
    const branchingHypBefore = hypsBeforeThatDisappeared[0];

    // 1. One hypBefore branched.
    hypsAfterThatAppeared.forEach((hypAfter) => {
      prettyHypNodes.push({
        text: hypAfter.type,
        name: hypAfter.username,
        id: hypAfter.id,
        isProof: hypAfter.isProof,
      });
    });
    if (hypsAfterThatAppeared.length > 0) {
      prettyHypArrows.push({
        fromId: branchingHypBefore.id,
        toIds: hypsAfterThatAppeared.map((hypAfter) => hypAfter.id),
        shardId: "temporary",
      });
    }

    // 2. And other hypBefores just disappeared!
    // Which we don't display, this will just be shown by hypothesis opacities
  }

  return [prettyHypNodes, prettyHypArrows];
};

// Any box is uniquely associated with a goal id.
// A particular goal id only ever belongs to some box.
const getBoxByGoalId = (pretty: ConvertedProofTree, goalId: string) => {
  return pretty.boxes.find((w) =>
    w.goalNodes.find((g) => g.id === getDisplayedId(pretty, goalId))
  );
};

export const getDisplayedId = (
  pretty: ConvertedProofTree,
  id: string | null
) => {
  if (id === null) {
    return null;
  }
  const displayedId = Object.keys(pretty.equivalentIds).find((displayedId) =>
    pretty.equivalentIds[displayedId].find((inferiorId) => inferiorId === id)
  );
  return displayedId ? displayedId : id;
};

// We always wanna talk to the representative of our equivalent goals.
// Representative goal id is the one that's actually drawn.
const addToEquivalentIds = (
  pretty: ConvertedProofTree,
  beforeId: string,
  afterId: string
) => {
  const existingGoal = pretty.equivalentIds[getDisplayedId(pretty, beforeId)!];
  if (existingGoal) {
    existingGoal.push(afterId);
  } else {
    pretty.equivalentIds[beforeId] = [afterId];
  }
};

const createNewBox = (pretty: ConvertedProofTree, parentId: string): Box => {
  const newBox = {
    id: newBoxId(),
    parentId: parentId,
    goalNodes: [],
    hypLayers: [],
    hypTables: [],
  };
  pretty.boxes.push(newBox);
  return newBox;
};

const handleTacticApp = (tactic: LeanTactic, pretty: ConvertedProofTree) => {
  const goalBefore = tactic.goalBefore;

  const currentBox = getBoxByGoalId(pretty, goalBefore.id);

  if (!currentBox) {
    console.warn("Couldn't find a box to place this tactic into.");
    console.log({ goalBefore });
    return;
  }

  const goalsAfter = [...tactic.goalsAfter];
  // 1. Draw goal nodes and arrows
  const prettyGoalArrows = [];
  let byBoxIds: string[] = [];
  let haveBoxIds: string[] = [];
  // CASE_1: this is likely a `have` tactic, so `spawnedGoals` are `have` boxes
  if (goalsAfter.length === 1 && goalsAfter[0].type === goalBefore.type) {
    // Sometimes the goal id changes but the type doesn't! Example: `let M := Nat.factorial N + 1; let p := Nat.minFac M`.
    // Future tactics will be referencing that id! So we mark it as equivalent to other goal ids.
    // In cases when goalsAfter.length > 1 we still want arrows. For example it was `cases h` where `h: q \or r`.
    addToEquivalentIds(pretty, goalBefore.id, tactic.goalsAfter[0].id);
    const boxes = tactic.spawnedGoals.map((goal) => {
      // Parent box is such that has our goalId as a hypothesis.
      // `have`'s fvarid won't equal `have's` mvarid however - so the only way to match them would be by the username. many `have`s may have the same username though, so let's just store out parentId.
      const newBox = createNewBox(pretty, "haveBox");
      newBox.goalNodes.push({
        text: goal.type,
        name: goal.username,
        id: goal.id,
      });
      return newBox;
    });
    haveBoxIds = boxes.map((b) => b.id);
  } else {
    // CASE_2: this is a tactic that has anonymous `by` calls (e.g. `apply MyTheorem (by positivity)`), so spawned subgoals are `byBox`es
    if (tactic.goalsAfter.length >= 1 && tactic.spawnedGoals.length >= 1) {
      const boxes = tactic.spawnedGoals.map((goal) => {
        const newBox = createNewBox(pretty, "byBox");
        newBox.goalNodes.push({
          text: goal.type,
          name: goal.username,
          id: goal.id,
        });
        return newBox;
      });
      byBoxIds = boxes.map((b) => b.id)
    // CASE_3: `spawnedGoals` are `calc` subgoals
    } else {
      goalsAfter.push(...tactic.spawnedGoals.map((goal) => ({ ...goal, isSpawned: true })));
    }

    for (const goal of goalsAfter) {
      prettyGoalArrows.push({
        fromId: goalBefore.id,
        toId: goal.id,
      });
    }
  }

  // 2. Draw boxes and hypotheses (if no bifurcation reuse the current box)
  const prettyHypArrows: Tactic["hypArrows"] = [];
  const tacticId = newTacticId();
  for (const goal of goalsAfter) {
    const [prettyHypNodes, prettyHypArrowsForAChild] = drawNewHypothesisLayer(
      pretty,
      goalBefore.hyps,
      goal.hyps
    );
    prettyHypArrows.push(...prettyHypArrowsForAChild);

    const box = goalsAfter.length > 1 ? createNewBox(pretty, currentBox.id) : currentBox;
    if (box.goalNodes[box.goalNodes.length - 1]?.text !== goal.type) {
      box.goalNodes.push({
        text: goal.type,
        name: goal.username,
        id: goal.id,
      });
    }
    if (prettyHypNodes.length > 0) {
      box.hypLayers.push({
        tacticId,
        hypNodes: prettyHypNodes,
      });
    }
  }

  pretty.tactics.push({
    id: tacticId,
    text: tactic.tacticString,
    dependsOnIds: tactic.tacticDependsOn,
    goalArrows: prettyGoalArrows,
    hypArrows: prettyHypArrows,
    successGoalId: goalsAfter.length === 0 ? goalBefore.id : undefined,
    haveBoxIds: haveBoxIds,
    byBoxIds: byBoxIds,
    position: tactic.position,
    theorems: tactic.theorems
  });
};

const drawInitialGoal = (
  leanProofTree: LeanProofTree,
  pretty: ConvertedProofTree
) => {
  const tacticId = newTacticId();

  const initialGoal: LeanGoal = leanProofTree[0].goalBefore;
  const hypNodes = initialGoal.hyps.map((hyp: LeanHypothesis) => ({
    text: hyp.type,
    name: hyp.username,
    id: hyp.id,
    isProof: hyp.isProof,
  }));
  const initialBox = {
    id: newBoxId(),
    parentId: null,
    goalNodes: [
      {
        text: initialGoal.type,
        name: initialGoal.username,
        id: initialGoal.id,
      },
    ],
    hypLayers:
      hypNodes.length > 0 ? [{ tacticId: tacticId, hypNodes: hypNodes }] : [],
    hypTables: [],
  };

  pretty.boxes.push(initialBox);
  pretty.tactics.push({
    id: tacticId,
    text: "init",
    dependsOnIds: [],
    goalArrows: [],
    hypArrows: [
      {
        fromId: null,
        toIds: hypNodes.map((hypNode) => hypNode.id),
        shardId: "temporary",
      },
    ],
    haveBoxIds: [],
    byBoxIds: [],
    position: { start: fakePosition, stop: fakePosition },
    theorems: []
  });
};

const postprocess = (pretty: ConvertedProofTree) => {
  pretty.tactics.forEach((tactic) => {
    tactic.goalArrows = tactic.goalArrows.map((goalArrow) => ({
      fromId: getDisplayedId(pretty, goalArrow.fromId)!,
      toId: getDisplayedId(pretty, goalArrow.toId)!,
    }));

    tactic.hypArrows = tactic.hypArrows.map((hypArrow, index) => ({
      shardId: index.toString(),
      fromId: getDisplayedId(pretty, hypArrow.fromId),
      toIds: hypArrow.toIds.map((toId) => getDisplayedId(pretty, toId)!),
    }));

    tactic.dependsOnIds = tactic.dependsOnIds.map(
      (id) => getDisplayedId(pretty, id)!
    );

    if (tactic.successGoalId) {
      tactic.successGoalId = getDisplayedId(pretty, tactic.successGoalId)!;
    }
  });

  return pretty;
};

// Note: we don't remove corresponding .dependsOn arrows here - in general we treat `.dependsOn` arrows liberally, and determine if some hypNode is present just by seeing if that element exists on frontend.
const removeParticularHypsFromTactic = (tactic: LeanTactic) => {
  [...tactic.goalsAfter, tactic.goalBefore, ...tactic.spawnedGoals].forEach(
    (goal) => {
      // ___Why remove ".universe" hypotheses?
      //    This is particularly necessary in Mathlib files - theorems there tend to have plenty of `variable () ()` hypotheses that have nothing to do with the proof.
      goal.hyps = goal.hyps.filter((hyp) => !(hyp.isProof === "universe"))
      // ___Why remove hypotheses with `✝` in the name?
      //  This usually means we are not intersted in this hypothesis, it just takes up space. E.g., if we did `rcases h with ⟨_, m⟩`, then we'll get hypotheses `left✝` and `m`.
      // && !hyp.username.includes('✝'))
    }
  );
};

// Account for steps which were generated due to backtracking. Only take the last from each goal.
// Assume that steps are returned in order of backtracking.
// example (p q : Prop) (hq : q) : p ∨ q := by
//   first | apply Or.inl; assumption | apply Or.inr; assumption
const filterBacktrackingSteps = (steps: LeanTactic[]): LeanTactic[] => {
  const result: LeanTactic[] = [];
  const fromGoals = steps.map((step) => step.goalBefore.id);
  for (let i = 0; i < steps.length; i++) {
    if (!fromGoals.slice(i + 1).includes(fromGoals[i])) {
      result.push(steps[i]);
    }
  }
  return result;
};

const converter = (leanProofTree: LeanProofTree): ConvertedProofTree => {
  boxId = 1;
  tacticId = 1;

  const convertedProofTree: ConvertedProofTree = {
    boxes: [],
    tactics: [],
    equivalentIds: {},
  };

  leanProofTree.forEach(removeParticularHypsFromTactic);
  leanProofTree = filterBacktrackingSteps(leanProofTree);

  // First of all, draw the INITIAL hypotheses and goal.
  drawInitialGoal(leanProofTree, convertedProofTree);
  // Then, draw all the other tactics and hypotheses and goals.
  leanProofTree.forEach((tactic) => {
    handleTacticApp(tactic, convertedProofTree);
  });

  postprocess(convertedProofTree);

  console.log({ leanProofTree, convertedProofTree });

  return convertedProofTree;
};

export default converter;
