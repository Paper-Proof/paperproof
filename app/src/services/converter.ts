import {
  LeanProofTree, LeanHypothesis, LeanTactic, LeanGoal,
  ConvertedProofTree, Tactic, HypNode
} from "types";

let boxId : number;
let tacticId : number;

const newBoxId = () => {
  return String(boxId++);
}

const newTacticId = () => {
  return String(tacticId++);
}

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
const weirdSituation = (pretty: ConvertedProofTree, hypAfter: LeanHypothesis) => {
  console.warn("Weird situation! Changing existingHypNode into hypAfter in-place:");
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
}

const drawNewHypothesisLayer = (pretty : ConvertedProofTree, hypsBefore : LeanHypothesis[], hypsAfter : LeanHypothesis[])
: [HypNode[], Tactic['hypArrows']] => {
  const prettyHypNodes: HypNode[] = [];
  const prettyHypArrows: Tactic['hypArrows'] = [];

  const hypsAfterMatched: LeanHypothesis[] = [];
  const hypsBeforeMatched: LeanHypothesis[] = [];

  // 1. Draw hypotheses that are clearly connected to a particular previous hypothesis
  hypsAfter.forEach((hypAfter) => {
    const hypBeforeById   = hypsBefore.find((hyp) => hyp.id === hypAfter.id);
    const hypBeforeByName = hypsBefore.find((hypBefore) =>
      (hypBefore.username === hypAfter.username) &&
      // Only match by username if that hypBefore wasn't already matched by id with someone else.
      // See github.com/antonkov/paper-proof/issues/10.
      !(hypsAfter.find((h) => h.id === hypBefore.id && h.id !== hypAfter.id))
    );

    if (hypBeforeById) {
      hypsAfterMatched.push(hypAfter);
      hypsBeforeMatched.push(hypBeforeById);

      if      (hypAfter.username === hypBeforeById.username && hypAfter.type === hypBeforeById.type) {
        // do nothing!
      }
      else if (hypAfter.username === hypBeforeById.username && hypAfter.type !== hypBeforeById.type) {
        weirdSituation(pretty, hypAfter);
      }
      else if (hypAfter.username !== hypBeforeById.username && hypAfter.type === hypBeforeById.type) {
        weirdSituation(pretty, hypAfter);
      }
      else if (hypAfter.username !== hypBeforeById.username && hypAfter.type !== hypBeforeById.type) {
        weirdSituation(pretty, hypAfter);
      }
    }
    else if (hypBeforeByName) {
      hypsAfterMatched.push(hypAfter);
      hypsBeforeMatched.push(hypBeforeByName);

      if      (hypAfter.id === hypBeforeByName.id && hypAfter.type === hypBeforeByName.type) {
        // do nothing!
      }
      else if (hypAfter.id === hypBeforeByName.id && hypAfter.type !== hypBeforeByName.type) {
        weirdSituation(pretty, hypAfter);
      }
      else if (hypAfter.id !== hypBeforeByName.id && hypAfter.type === hypBeforeByName.type) {
        // don't create any new nodes or arrows, just add `hypAfter.id` to equivalentIds
        addToEquivalentIds(pretty, hypBeforeByName.id, hypAfter.id);
      }
      else if (hypAfter.id !== hypBeforeByName.id && hypAfter.type !== hypBeforeByName.type) {
        // draw a new node, draw an arrow
        prettyHypNodes.push({
          text: hypAfter.type,
          name: hypAfter.username,
          id  : hypAfter.id,
          isProof: hypAfter.isProof
        });

        prettyHypArrows.push({
          fromId: hypBeforeByName.id,
          toIds : [hypAfter.id]
        });
      }
    }
  });

  // 2. Draw hypotheses that disappeared and appeared out of nowhere
  const hypsBeforeThatDisappeared = hypsBefore.filter((hyp) => !hypsBeforeMatched.some((matchedHyp) => matchedHyp.id === hyp.id));
  const hypsAfterThatAppeared = hypsAfter.filter((hyp) => !hypsAfterMatched.some((matchedHyp) => matchedHyp.id === hyp.id));

  // - if 0 hypotheses disappeared, and 0 hypotheses appeared, do nothing!
  if (hypsBeforeThatDisappeared.length === 0 && hypsAfterThatAppeared.length === 0) {
    // done :-)
  }
  // - if 0 hypotheses disappeared, and X hypotheses appeared, draw { null → id } arrows [many nulls!]
  else if (hypsBeforeThatDisappeared.length === 0 && hypsAfterThatAppeared.length > 0) {
    hypsAfterThatAppeared.forEach((hypAfter) => {
      prettyHypNodes.push({
        text: hypAfter.type,
        name: hypAfter.username,
        id  : hypAfter.id,
        isProof: hypAfter.isProof
      });
    });
    if (hypsAfterThatAppeared.length > 0) {
      prettyHypArrows.push({
        fromId: null,
        toIds : hypsAfterThatAppeared.map((hypAfter) => hypAfter.id)
      });
    }
  }
  // - if X hypotheses disappeared, and 0 hypotheses appeared - don't draw anything
  else if (hypsBeforeThatDisappeared.length > 0 && hypsAfterThatAppeared.length === 0) {
    // Don't draw anything, this will be indicated by opacities
  }
  // - if X hypotheses disappeared, and X hypotheses appeared, draw { everything → everything } arrows
  else if (hypsBeforeThatDisappeared.length > 0 && hypsAfterThatAppeared.length > 0) {
    // The 2nd part of this `else if` doesn't ever happen as far as we're aware -
    // When we actually stumble upon a tactic that does that, we'll see how good our handling of this is.
    if (hypsBeforeThatDisappeared.length > 1 && hypsAfterThatAppeared.length > 0) {
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
        id  : hypAfter.id,
        isProof: hypAfter.isProof
      });
    });
    if (hypsAfterThatAppeared.length > 0) {
      prettyHypArrows.push({
        fromId: branchingHypBefore.id,
        toIds : hypsAfterThatAppeared.map((hypAfter) => hypAfter.id)
      });
    }

    // 2. And other hypBefores just disappeared!
    // Which we don't display, this will just be shown by hypothesis opacities
  }

  return [prettyHypNodes.reverse(), prettyHypArrows];
}

// Any box is uniquely associated with a goal id.
// A particular goal id only ever belongs to some box. 
const getBoxByGoalId = (pretty : ConvertedProofTree, goalId : string) => {
  return pretty.boxes.find((w) =>
    w.goalNodes.find((g) => g.id === getDisplayedId(pretty, goalId))
  )
}

export const getDisplayedId = (pretty : ConvertedProofTree, id : string | null) => {
  if (id === null) {
    return null
  }
  const displayedId = Object.keys(pretty.equivalentIds).find((displayedId) =>
    pretty.equivalentIds[displayedId].find((inferiorId) => inferiorId === id)
  );
  return displayedId ? displayedId : id;
}

// We always wanna talk to the representative of our equivalent goals.
// Representative goal id is the one that's actually drawn. 
const addToEquivalentIds = (pretty : ConvertedProofTree, beforeId : string, afterId : string) => {
  const existingGoal = pretty.equivalentIds[getDisplayedId(pretty, beforeId)!];
  if (existingGoal) {
    existingGoal.push(afterId);
  } else {
    pretty.equivalentIds[beforeId] = [afterId];
  }
}

const handleTacticApp = (
  tactic: LeanTactic,
  pretty: ConvertedProofTree,
  haveBoxIds: string[] = []
) => {
  // We assume `tactic.goalsBefore[0]` is always the goal the tactic worked on!
  // Is it fair to assume? So far seems good.
  const mainGoalBefore = tactic.goalsBefore[0];

  let currentBox = getBoxByGoalId(pretty, mainGoalBefore.id);

  if (!currentBox) {
    console.warn("Couldn't find a box to place this tactic into.");
    console.log({ mainGoalBefore });
    return;
  }

  const relevantGoalsAfter = tactic.goalsAfter
    .filter(
      (goalAfter) =>
        !tactic.goalsBefore.find(
          (goalBefore) => goalBefore.username === goalAfter.username
        ) || mainGoalBefore.username === goalAfter.username
    )
    .sort((a, b) => a.id.localeCompare(b.id));

  // - we solved the goal!
  if (relevantGoalsAfter.length === 0) {
    const nextGoal = tactic.goalsAfter[0];

    // `done` has a very unusual behaviour -
    // if we had some goals prior to it, then it's a "fake success" tactic for all of them
    if (tactic.tacticString === "done") {
      tactic.goalsBefore.forEach((goalBefore) => {
        pretty.tactics.push({
          id: newTacticId(),
          text: "done",
          dependsOnIds: [],
          goalArrows: [],
          hypArrows: [],
          successGoalId: goalBefore.id,
          haveBoxIds: haveBoxIds,
        });
      })
    } else {
      pretty.tactics.push({
        id: newTacticId(),
        text: tactic.tacticString,
        dependsOnIds: tactic.tacticDependsOn,
        goalArrows: [],
        hypArrows: [],
        successGoalId: mainGoalBefore.id,
        haveBoxIds: haveBoxIds,
      });
    }
  }
  // - we updated the goal!
  else if (relevantGoalsAfter.length === 1) {
    const updatedGoal = relevantGoalsAfter[0];

    // 1. Draw goal nodes and arrows
    let prettyGoalArrows: Tactic["goalArrows"] = [];
    // In general, we would want to do this:
    // `if (mainGoalBefore.type !== updatedGoal.type) {`
    // However sometimes the goal id changes; and the type doesn't! Example: `let M := Nat.factorial N + 1; let p := Nat.minFac M`.
    // In such cases, we still want to put this goalNode into our box - to enable future tactics to find this box by goal id.
    // Also: future tactics might well be referencing that id! So we, of course, need to mark it as equivalent to other goal ids.
    if (mainGoalBefore.type === updatedGoal.type) {
      addToEquivalentIds(pretty, mainGoalBefore.id, updatedGoal.id);
    } else {
      currentBox.goalNodes.push({
        text: updatedGoal.type,
        name: updatedGoal.username,
        id: updatedGoal.id,
      });
      prettyGoalArrows = [
        {
          fromId: mainGoalBefore.id,
          toId: updatedGoal.id,
        },
      ];
    }

    // 2. Draw hypothesis nodes and arrows
    const hypsBefore = mainGoalBefore.hyps;
    const hypsAfter = updatedGoal.hyps;
    let [prettyHypNodes, prettyHypArrows] = drawNewHypothesisLayer(
      pretty,
      hypsBefore,
      hypsAfter
    );

    const tacticId : string = newTacticId();

    if (prettyHypNodes.length > 0) {
      currentBox.hypLayers.push({
        tacticId: tacticId,
        hypNodes: prettyHypNodes
      });
    }

    pretty.tactics.push({
      id: tacticId,
      text: tactic.tacticString,
      dependsOnIds: tactic.tacticDependsOn,
      goalArrows: prettyGoalArrows,
      hypArrows: prettyHypArrows,
      haveBoxIds: haveBoxIds,
    });
  }
  // - we forked the goal!
  else if (relevantGoalsAfter.length > 1) {
    // 1. Draw goal nodes and arrows
    const prettyGoalArrows = relevantGoalsAfter.map((goal) => ({
      fromId: mainGoalBefore.id,
      toId: goal.id,
    }));

    const prettyHypArrows: Tactic["hypArrows"] = [];
    const tacticId = newTacticId();
    // We are creating new child boxes
    const childBoxes = relevantGoalsAfter.map((goal) => {
      const hypsBefore = mainGoalBefore.hyps;
      const hypsAfter = goal.hyps;
      const [prettyHypNodes, prettyHypArrowsForAChild] = drawNewHypothesisLayer(
        pretty,
        hypsBefore,
        hypsAfter
      );
      prettyHypArrows.push(...prettyHypArrowsForAChild);

      return {
        id: newBoxId(),
        parentId: currentBox!.id,
        goalNodes: [
          {
            text: goal.type,
            name: goal.username,
            id: goal.id,
          },
        ],
        hypLayers: prettyHypNodes.length > 0 ? [{ tacticId, hypNodes: prettyHypNodes }] : [],
      };
    });
    pretty.boxes.push(...childBoxes);

    pretty.tactics.push({
      id: tacticId,
      text: tactic.tacticString,
      dependsOnIds: tactic.tacticDependsOn,
      goalArrows: prettyGoalArrows,
      hypArrows: prettyHypArrows,
      haveBoxIds: haveBoxIds,
    });
  }
};

const drawInitialGoal = (leanProofTree: LeanProofTree, pretty: ConvertedProofTree) => {
  const tacticId = newTacticId();

  const initialGoal : LeanGoal = getInitialGoal(leanProofTree)!;
  const hypNodes = initialGoal.hyps.map((hyp: LeanHypothesis) => ({
    text: hyp.type,
    name: hyp.username,
    id: hyp.id,
    isProof: hyp.isProof
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
    hypLayers: hypNodes.length > 0 ? [{ tacticId: tacticId, hypNodes: hypNodes.reverse() }] : [],
  };

  pretty.boxes.push(initialBox);
  pretty.tactics.push({
    id: tacticId,
    text: "init",
    dependsOnIds: [],
    goalArrows: [],
    hypArrows: [{ fromId: null, toIds: hypNodes.map((hypNode) => hypNode.id) }],
    haveBoxIds: []
  });
};

// TODO: Refactor it since this function relies on obsolete assumptions:
// - There is only one initial goal (can be multiple `have <p, q> := <by rfl, by rfl>`)
// - Order of tactics in steps reflects the order of the proof.
const getInitialGoal = (subSteps: LeanProofTree): LeanGoal | undefined => {
  const firstStep = subSteps[0];
  if ("tacticApp" in firstStep) {
    return firstStep.tacticApp.t.goalsBefore[0];
  } else if ("haveDecl" in firstStep) {
    return firstStep.haveDecl.t.goalsBefore[0];
  }
};

const recursive = (subSteps: LeanProofTree, pretty: ConvertedProofTree) => {
  subSteps.forEach((subStep) => {
    if ("tacticApp" in subStep) {
      handleTacticApp(subStep.tacticApp.t, pretty);
    } else if ("haveDecl" in subStep) {
      // TODO: Remove when new lean version reporting is set up.
      const initialGoals =
        "initialGoals" in subStep.haveDecl
          ? subStep.haveDecl.initialGoals
          : [getInitialGoal(subStep.haveDecl.subSteps)!];
      const boxes = initialGoals.map((goal) => ({
        id: newBoxId(),
        // Parent box is such that has our goalId as a hypothesis.
        // `have`'s fvarid won't equal `have's` mvarid however - so the only way to match them would be by the username. many `have`s may have the same username though, so let's just store out parentId.
        parentId: "haveBox",
        goalNodes: [
          {
            text: goal.type,
            name: goal.username,
            id: goal.id,
          },
        ],
        // `have`s don't introduce any new hypotheses
        hypLayers: [],
      }));

      handleTacticApp(
        subStep.haveDecl.t,
        pretty,
        boxes.map((w) => w.id)
      );
      pretty.boxes.push(...boxes);

      recursive(subStep.haveDecl.subSteps, pretty);
    }
  });
};

const postprocess = (pretty: ConvertedProofTree) => {
  pretty.tactics.forEach((tactic) => {
    tactic.goalArrows = tactic.goalArrows.map((goalArrow) => ({
      fromId: getDisplayedId(pretty, goalArrow.fromId)!,
      toId  : getDisplayedId(pretty, goalArrow.toId)!
    }));

    tactic.hypArrows = tactic.hypArrows.map((hypArrow, index) => ({
      shardId: index.toString(),
      fromId: getDisplayedId(pretty, hypArrow.fromId),
      toIds : hypArrow.toIds.map((toId) => getDisplayedId(pretty, toId)!)
    }));

    tactic.dependsOnIds = tactic.dependsOnIds.map((id) =>
      getDisplayedId(pretty, id)!
    );

    if (tactic.successGoalId) {
      tactic.successGoalId = getDisplayedId(pretty, tactic.successGoalId)!;
    }
  });

  return pretty
}

const removeUniverseHypsFromTactic = (tactic: LeanTactic) => {
  tactic.goalsAfter.forEach((goal) => {
    goal.hyps = goal.hyps.filter((hyp) => !(hyp.isProof === "universe"))
  });
  tactic.goalsBefore.forEach((goal) => {
    goal.hyps = goal.hyps.filter((hyp) => !(hyp.isProof === "universe"))
  });
}

const preprocess = (subSteps: LeanProofTree) => {
  // Remove all ".universe" hypotheses.
  // This is particularly necessary in Mathlib files - theorems there tend to have plenty of `variable () ()` hypotheses that have nothing to do with the proof. 
  // Note: we don't remove corresponding .dependsOn arrows here - in general we treat `.dependsOn` arrows liberally, and determine if some hypNode is present just by seeing if that element exists on frontend.
  subSteps.forEach((subStep) => {
    if ("tacticApp" in subStep) {
      removeUniverseHypsFromTactic(subStep.tacticApp.t);
    } else if ("haveDecl" in subStep) {
      removeUniverseHypsFromTactic(subStep.haveDecl.t);
      preprocess(subStep.haveDecl.subSteps);
    }
  });
}

const converter = (leanProofTree: LeanProofTree) : ConvertedProofTree => {
  boxId = 1;
  tacticId = 1;

  const convertedProofTree : ConvertedProofTree = {
    boxes: [],
    tactics: [],
    equivalentIds: {},
  }

  preprocess(leanProofTree);

  // First of all, draw the INITIAL hypotheses and goal.
  drawInitialGoal(leanProofTree, convertedProofTree);
  // Then, draw all the other tactics and hypotheses and goals.
  recursive(leanProofTree, convertedProofTree);

  postprocess(convertedProofTree);

  console.log({ leanProofTree, convertedProofTree });

  return convertedProofTree;
}

export default converter;
