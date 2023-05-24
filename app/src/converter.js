// import { createRequire } from 'module';
// const require = createRequire(import.meta.url);
// const util = require('util');

// import infoTreeExample from './infoTreeExample.js';

const drawNewHypotheses = (hypsBefore, hypsAfter) => {
  const prettyHypNodes = [];
  let prettyHypArrows = [];

  // 1. Determine which hypotheses disappeared and appeared username-wise
  const hypsBeforeUsernames = hypsBefore.map((hyp) => hyp.username);
  const hypsAfterUsernames  = hypsBefore.map((hyp) => hyp.username);
  const hypsBeforeThatDisappeared = hypsBefore.filter((hyp) => !hypsAfterUsernames.includes(hyp.username));
  const hypsAfterThatAppeared     = hypsAfter.filter((hyp) => !hypsBeforeUsernames.includes(hyp.username));

  // 2. Draw them!
  // - if 0 hypotheses disappeared, and 0 hypotheses appeared, do nothing!
  if (hypsBeforeThatDisappeared.length === 0 && hypsAfterThatAppeared.length === 0) {
    // done :-)
  }
  // - if 0 hypotheses disappeared, and X hypotheses appeared, draw { null → id } arrows [many nulls!]
  else if (hypsBeforeThatDisappeared.length === 0 && hypsAfterThatAppeared.length > 0) {
    const newHypNodes = hypsAfterThatAppeared.map((hyp) => ({
      text: hyp.type,
      name: hyp.username,
      id  : hyp.id
    }));
    prettyHypNodes.push(...newHypNodes);

    prettyHypArrows = newHypNodes.map((hypNode) => ({
      fromId: null,
      toId: hypNode.id
    }));
  }
  // - if X hypotheses disappeared, and 0 hypotheses appeared, draw { id → null } arrows [many nulls!]
  else if (hypsBeforeThatDisappeared.length > 0 && hypsAfterThatAppeared.length === 0) {
    prettyHypArrows = hypsBeforeThatDisappeared.map((hyp) => ({
      fromId: hyp.id,
      toId: null
    }));
  }
  // - if X hypotheses disappeared, and X hypotheses appeared, draw { everything → everything } arrows
  else if (hypsBeforeThatDisappeared.length > 0 && hypsAfterThatAppeared.length > 0) {
    hypsBeforeThatDisappeared.forEach((hypBefore) => {
      hypsAfterThatAppeared.forEach((hypAfter) => {
        prettyHypArrows.push({
          fromId: hypBefore.id,
          toId: hypAfter.id
        });
      });
    });
  }

  // 3. Then, independently, draw all the `.type` changes for hyps that stayed with the same username!
  hypsAfter.forEach((hypAfter) => {
    const hypBeforeWithSameUsername = hypsBefore.find((hypBefore) => hypBefore.username == hypAfter.username);
    if (hypBeforeWithSameUsername && hypBeforeWithSameUsername.type !== hypAfter.type) {
      prettyHypNodes.push({
        text: hypAfter.type,
        name: hypAfter.username,
        id  : hypAfter.id
      });
      prettyHypArrows.push({
        fromId: hypBefore.id,
        toId: hypAfter.id
      });
    }
  });

  return [prettyHypNodes, prettyHypArrows]
}

// Any window is uniquely associated with a goal id.
// A particular goal id only ever belongs to some window. 
const getWindowByGoalId = (windows, goalId) => {
  return windows.find((w) =>
    w.goalNodes.find((g) => g.id === goalId)
  )
}

export const toEdges = (infoTreeVast) => {
  const infoTree = infoTreeVast.map((li) => li.tacticApp.t);

  const pretty = {
    windows: [],
    tactics: []
  }
  let newWindowId = 0;

  // First of all, draw the INITIAL hypotheses and goal.
  const initialMainGoal = infoTree[0].goalsBefore[0];
  let initialWindow = {
    id: newWindowId,
    parentId: null,
    goalNodes: [
      {
        text: initialMainGoal.type,
        id  : initialMainGoal.id
      }
    ],
    hypNodes: [
      initialMainGoal.hyps.map((hyp) => ({
        text: hyp.type,
        name: hyp.username,
        id  : hyp.id
      }))
    ]
  };
  pretty.windows.push(initialWindow);

  // Then, draw all the other tactics and hypotheses and goals.
  infoTree.forEach((tactic) => {
    // We assume `tactic.goalsBefore[0]` is always the goal the tactic worked on!
    // Is it fair to assume? So far seems good.
    const mainGoalBefore = tactic.goalsBefore[0];
    const currentWindow = getWindowByGoalId(pretty.windows, mainGoalBefore.id);

    const relevantGoalsAfter = tactic.goalsAfter
      .filter((goalAfter) =>
        !tactic.goalsBefore.find((goalBefore) => goalBefore.username === goalAfter.username) ||
        mainGoalBefore.username === goalAfter.username
      );

    // - we solved the goal!
    if (relevantGoalsAfter.length === 0) {
      const nextGoal = tactic.goalsAfter[0];

      pretty.tactics.push({
        text         : tactic.tacticString,
        dependsOnIds : tactic.tacticDependsOn,
        goalArrows   : [],
        hypArrows    : [],
        // success arrows are better not drawn (noisy!), we should just mark the tactic as 🎉.
        // .dependsOnIds will convey all the information we want to see.
        isSuccess    : nextGoal ? '🎉' : 'For all goals, 🎉!',
        successGoalId: mainGoalBefore.id
      });
    }
    // - we updated the goal!
    else if (relevantGoalsAfter.length === 1) { 
      const updatedGoal = relevantGoalsAfter[0];

      // 1. Draw goal nodes and arrows
      let prettyGoalArrows = [];
      if (mainGoalBefore.type !== updatedGoal.type) {
        currentWindow.goalNodes.push({
          text: updatedGoal.type,
          id  : updatedGoal.id
        });
        prettyGoalArrows = [{
          fromId: mainGoalBefore.id,
          toId: updatedGoal.id
        }];
      }

      // 2. Draw hypothesis nodes and arrows
      const hypsBefore = mainGoalBefore.hyps;
      const hypsAfter  = updatedGoal.hyps;
      let [prettyHypNodes, prettyHypArrows] = drawNewHypotheses(hypsBefore, hypsAfter);
      if (prettyHypNodes.length > 0) {
        currentWindow.hypNodes.push(prettyHypNodes);
      }

      pretty.tactics.push({
        text         : tactic.tacticString,
        dependsOnIds : tactic.tacticDependsOn,
        goalArrows   : prettyGoalArrows,
        hypArrows    : prettyHypArrows,
        isSuccess    : false
      });
    }
    // - we forked the goal!
    else if (relevantGoalsAfter.length > 1) {
      // 1. Draw goal nodes and arrows
      const prettyGoalArrows = relevantGoalsAfter.map((goal) => ({
        fromId: mainGoalBefore.id,
        toId: goal.id
      }));

      const prettyHypArrows = [];
      // We are creating new child windows
      const childWindows = relevantGoalsAfter.map((goal) => {
        const hypsBefore = mainGoalBefore.hyps;
        const hypsAfter  = goal.hyps;
        const [prettyHypNodes, prettyHypArrowsForAChild] = drawNewHypotheses(hypsBefore, hypsAfter);
        prettyHypArrows.push(...prettyHypArrowsForAChild);

        return {
          id: ++newWindowId,
          parentId: currentWindow.id,
          goalNodes: [
            {
              text: goal.type,
              id: goal.id
            }
          ],
          hypNodes: prettyHypNodes.length > 0 ? [prettyHypNodes] : []
        }
      });
      pretty.windows.push(...childWindows);

      pretty.tactics.push({
        text         : tactic.tacticString,
        dependsOnIds : tactic.tacticDependsOn,
        goalArrows   : prettyGoalArrows,
        hypArrows    : prettyHypArrows,
        isSuccess    : false
      });
    }
  })

  return pretty
}


// const edges = toEdges(infoTreeExample)
// console.log(util.inspect(edges, { depth: null }));
