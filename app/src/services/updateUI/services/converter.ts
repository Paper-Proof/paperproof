import { ConvertedProofTree, LeanProofTree, Tactic, Window, LeanHypothesis, LeanTactic, LeanGoal, HypNode } from "types";

let windowId : number;
let tacticId : number;

const newWindowId = () => {
  return String(windowId++);
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
// IF we stumble upon the situation where this behaviour is undesirable - let's create a complex data structure that creates new fake ids; and keep track of them in a way that accounts for window parenthood relationships.
const weirdSituation = (pretty: ConvertedProofTree, hypAfter: LeanHypothesis) => {
  console.warn("Weird situation! Changing existingHypNode into hypAfter in-place:");
  // We need a displayed id here [because, unusually enough, we're changing the already-drawn node]
  const hypAfterId = getDisplayedId(pretty, hypAfter.id);
  pretty.windows.forEach((w) => {
    w.hypNodes.forEach((hypLevel) => {
      hypLevel.forEach((existingHypNode) => {
        if (existingHypNode.id === hypAfterId) {
          console.log({ existingHypNode, hypAfter });
          existingHypNode.name = hypAfter.username;
          existingHypNode.text = hypAfter.type;
        }
      });
    });
  });
}

const drawNewHypothesisLayer = (pretty : ConvertedProofTree, hypsBefore : LeanHypothesis[], hypsAfter : LeanHypothesis[]) => {
  const prettyHypNodes: HypNode[] = [];
  const prettyHypArrows: any[] = [];

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
          id  : hypAfter.id
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
        id  : hypAfter.id
      });
    });
    if (hypsAfterThatAppeared.length > 0) {
      prettyHypArrows.push({
        fromId: null,
        toIds : hypsAfterThatAppeared.map((hypAfter) => hypAfter.id)
      });
    }
  }
  // - if X hypotheses disappeared, and 0 hypotheses appeared, draw { id → null } arrows
  else if (hypsBeforeThatDisappeared.length > 0 && hypsAfterThatAppeared.length === 0) {
    hypsBeforeThatDisappeared.forEach((hypBefore) => {
      prettyHypNodes.push({
        text: null,
        name: null,
        id  : `${hypBefore.id}-null`
      });

      prettyHypArrows.push({
        fromId: hypBefore.id,
        toIds : [`${hypBefore.id}-null`]
      });
    });
  }
  // - if X hypotheses disappeared, and X hypotheses appeared, draw { everything → everything } arrows
  else if (hypsBeforeThatDisappeared.length > 0 && hypsAfterThatAppeared.length > 0) {
    // The 2nd part of this `else if` doesn't ever happen as far as we're aware -
    // When we actually stumble upon a tactic that does that, we'll see how good our handling of this is.
    if (hypsBeforeThatDisappeared.length > 1 && hypsAfterThatAppeared.length > 0) {
      alert("FINALLY; We have stumbled upon the mysterious tactic that makes 2 hypotheses join into 1 hypothesis");
    }

    // `branchingHypBefore` is taken to be the 1st hyp, but we could have taken any hypothesis.
    // Theoretically, there is only ever 1 hypothesis here.
    const branchingHypBefore = hypsBeforeThatDisappeared[0];

    // 1. One hypBefore branched.
    hypsAfterThatAppeared.forEach((hypAfter) => {
      prettyHypNodes.push({
        text: hypAfter.type,
        name: hypAfter.username,
        id  : hypAfter.id
      });
    });
    if (hypsAfterThatAppeared.length > 0) {
      prettyHypArrows.push({
        fromId: branchingHypBefore.id,
        toIds : hypsAfterThatAppeared.map((hypAfter) => hypAfter.id)
      });
    }

    // 2. And other hypBefores just disappeared!
    const restOfHypsBefore = hypsBeforeThatDisappeared.slice(1);
    restOfHypsBefore.forEach((hypBefore) => {
      prettyHypNodes.push({
        text: null,
        name: null,
        id  : `${hypBefore.id}-null`
      });
      prettyHypArrows.push({
        fromId: hypBefore.id,
        toIds : [`${hypBefore.id}-null`]
      });
    });
  }

  return [prettyHypNodes.reverse(), prettyHypArrows];
}

// Any window is uniquely associated with a goal id.
// A particular goal id only ever belongs to some window. 
const getWindowByGoalId = (pretty : ConvertedProofTree, goalId : string) => {
  return pretty.windows.find((w) =>
    w.goalNodes.find((g) => g.id === getDisplayedId(pretty, goalId))
  )
}

const getDisplayedId = (pretty : ConvertedProofTree, id : string | null) => {
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
  haveWindowIds: string[] = []
) => {
  // We assume `tactic.goalsBefore[0]` is always the goal the tactic worked on!
  // Is it fair to assume? So far seems good.
  const mainGoalBefore = tactic.goalsBefore[0];

  let currentWindow = getWindowByGoalId(pretty, mainGoalBefore.id);

  if (!currentWindow) {
    console.warn("Couldn't find a window to place this tactic into.");
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

    pretty.tactics.push({
      id: newTacticId(),
      text: tactic.tacticString,
      dependsOnIds: tactic.tacticDependsOn,
      goalArrows: [],
      hypArrows: [],
      // success arrows are better not drawn (noisy!), we should just mark the tactic as 🎉.
      // .dependsOnIds will convey all the information we want to see.
      isSuccess: nextGoal ? "🎉" : "For all goals, 🎉!",
      successGoalId: mainGoalBefore.id,
      haveWindowIds,
    });
  }
  // - we updated the goal!
  else if (relevantGoalsAfter.length === 1) {
    const updatedGoal = relevantGoalsAfter[0];

    // 1. Draw goal nodes and arrows
    let prettyGoalArrows: Tactic["goalArrows"] = [];
    // In general, we would want to do this:
    // `if (mainGoalBefore.type !== updatedGoal.type) {`
    // However sometimes the goal id changes; and the type doesn't! Example: `let M := Nat.factorial N + 1; let p := Nat.minFac M`.
    // In such cases, we still want to put this goalNode into our window - to enable future tactics to find this window by goal id.
    // Also: future tactics might well be referencing that id! So we, of course, need to mark it as equivalent to other goal ids.
    if (mainGoalBefore.type === updatedGoal.type) {
      addToEquivalentIds(pretty, mainGoalBefore.id, updatedGoal.id);
    } else {
      currentWindow.goalNodes.push({
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

    if (prettyHypNodes.length > 0) {
      currentWindow.hypNodes.push(prettyHypNodes);
    }

    pretty.tactics.push({
      id: newTacticId(),
      text: tactic.tacticString,
      dependsOnIds: tactic.tacticDependsOn,
      goalArrows: prettyGoalArrows,
      hypArrows: prettyHypArrows,
      isSuccess: false,
      haveWindowIds,
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
    // We are creating new child windows
    const childWindows = relevantGoalsAfter.map((goal) => {
      const hypsBefore = mainGoalBefore.hyps;
      const hypsAfter = goal.hyps;
      const [prettyHypNodes, prettyHypArrowsForAChild] = drawNewHypothesisLayer(
        pretty,
        hypsBefore,
        hypsAfter
      );
      prettyHypArrows.push(...prettyHypArrowsForAChild);

      return {
        id: newWindowId(),
        parentId: currentWindow!.id,
        goalNodes: [
          {
            text: goal.type,
            name: goal.username,
            id: goal.id,
          },
        ],
        hypNodes: prettyHypNodes.length > 0 ? [prettyHypNodes] : [],
      };
    });
    pretty.windows.push(...childWindows);

    pretty.tactics.push({
      id: newTacticId(),
      text: tactic.tacticString,
      dependsOnIds: tactic.tacticDependsOn,
      goalArrows: prettyGoalArrows,
      hypArrows: prettyHypArrows,
      isSuccess: false,
      haveWindowIds,
    });
  }
};

const drawInitialGoal = (
  initialMainGoal: LeanGoal,
  pretty: ConvertedProofTree
) => {
  const hypNodes = initialMainGoal.hyps.map((hyp: LeanHypothesis) => ({
    text: hyp.type,
    name: hyp.username,
    id: hyp.id,
  }));
  const initialWindow = {
    id: newWindowId(),
    parentId: null,
    goalNodes: [
      {
        text: initialMainGoal.type,
        name: initialMainGoal.username,
        id: initialMainGoal.id,
      },
    ],
    hypNodes: hypNodes.length > 0 ? [hypNodes.reverse()] : [],
  };
  pretty.windows.push(initialWindow);
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
      const windows = initialGoals.map((goal) => ({
        id: newWindowId(),
        // Parent window is such that has our goalId as a hypothesis.
        // `have`'s fvarid won't equal `have's` mvarid however - so the only way to match them would be by the username. many `have`s may have the same username though, so let's just store out parentId.
        parentId: "haveWindow",
        goalNodes: [
          {
            text: goal.type,
            name: goal.username,
            id: goal.id,
          },
        ],
        // `have`s don't introduce any new hypotheses
        hypNodes: [],
      }));

      handleTacticApp(
        subStep.haveDecl.t,
        pretty,
        windows.map((w) => w.id)
      );
      pretty.windows.push(...windows);

      recursive(subStep.haveDecl.subSteps, pretty);
    }
  });
};

const postprocess = (pretty: ConvertedProofTree): ConvertedProofTree => {
  pretty.tactics.forEach((tactic) => {
    tactic.goalArrows = tactic.goalArrows.map((goalArrow) => ({
      fromId: getDisplayedId(pretty, goalArrow.fromId)!,
      toId  : getDisplayedId(pretty, goalArrow.toId)!
    }));

    tactic.hypArrows = tactic.hypArrows.map((hypArrow) => ({
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

const converter = (leanProofTree: LeanProofTree) : ConvertedProofTree => {
  windowId = 1;
  tacticId = 1;

  const pretty : ConvertedProofTree = {
    windows: [],
    tactics: [],
    equivalentIds: {},
  }

  // First of all, draw the INITIAL hypotheses and goal.
  const initialGoal : LeanGoal = getInitialGoal(leanProofTree)!;
  drawInitialGoal(initialGoal, pretty);

  // Then, draw all the other tactics and hypotheses and goals.
  recursive(leanProofTree, pretty);

  return postprocess(pretty);
}

export default converter;
