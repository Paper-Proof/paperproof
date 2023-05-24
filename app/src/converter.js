import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const util = require('util');

import infoTreeExample from './infoTreeExample.js';

const drawNewHypotheses = (hypsBefore, hypsAfter) => {
  const prettyHypNodes = [];
  let prettyHypArrows = [];

  // 1. Determine what new hypotheses we wanna draw
  const hypsBeforeUsernames = hypsBefore.map((hyp) => hyp.username);
  const hypsAfterUsernames  = hypsBefore.map((hyp) => hyp.username);
  const hypsBeforeThatDisappeared = hypsBefore.filter((hyp) => !hypsAfterUsernames.includes(hyp.username));
  const hypsAfterThatAppeared     = hypsAfter.filter((hyp) => !hypsBeforeUsernames.includes(hyp.username));

  // 2. Draw the hypotheses!
  // - if 0 hypotheses disappeared, and 0 hypotheses appeared, do nothing!
  if (hypsBeforeThatDisappeared.length === 0 && hypsAfterThatAppeared.length === 0) {
    // done :-)
  // - if 0 hypotheses disappeared, and X hypotheses appeared, draw { null → id } arrows [many nulls!]
  } else if (hypsBeforeThatDisappeared.length === 0 && hypsAfterThatAppeared.length > 0) {
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
  // - if X hypotheses disappeared, and 0 hypotheses appeared, draw { id → null } arrows [many nulls!]
  } else if (hypsBeforeThatDisappeared.length > 0 && hypsAfterThatAppeared.length === 0) {
    prettyHypArrows = hypsBeforeThatDisappeared.map((hyp) => ({
      fromId: hyp.id,
      toId: null
    }));
  // - if X hypotheses disappeared, and X hypotheses appeared, draw { everything → everything } arrows
  } else if (hypsBeforeThatDisappeared.length > 0 && hypsAfterThatAppeared.length > 0) {
    hypsBeforeThatDisappeared.forEach((hypBefore) => {
      hypsAfterThatAppeared.forEach((hypAfter) => {
        prettyHypArrows.push({
          fromId: hypBefore.id,
          toId: hypAfter.id
        });
      });
    });
  }

  // 3. Then, independently, draw all the `.type` changes for hyps that stayed the same!
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

  const initialMainGoal = infoTree[0].goalsBefore[0];
  // First of all, draw the INITIAL hypotheses and goals.
  let newId = 0
  let initialWindow = {
    id: newId,
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
  let currentWindow = initialWindow;

  // Then, draw all the other tactics and hypotheses and goals.
  infoTree.forEach((tactic) => {
    let prettyGoalArrows  = [];

    // We assume `tactic.goalsBefore[0]` is always the goal the tactic worked on!
    // Is it fair to assume? So far seems good.
    const mainGoalBefore = tactic.goalsBefore[0];

    // 1. Determine what new goals we wanna draw
    const irrelevantGoalNames = tactic.goalsBefore
      .filter((goalBefore) =>
        goalBefore.username !== mainGoalBefore.username
      )
      .map((goalBefore) => goalBefore.username);
    const relevantGoalsAfter = tactic.goalsAfter
      .filter((goalAfter) =>
        !irrelevantGoalNames.includes(goalAfter.username)
      );

    // 2. Draw the goals!
    // - we solved the goal!
    if (relevantGoalsAfter.length === 0) {
      const nextGoal = tactic.goalsAfter[0];

      pretty.tactics.push({
        text         : tactic.tacticString,
        dependsOnIds : tactic.tacticDependsOn,
        goalArrows   : [],
        hypArrows    : [],
        isSuccess    : nextGoal ? '🎉' : 'For all goals, 🎉!',
        successGoalId: mainGoalBefore.id
      });

      if (nextGoal) {
        currentWindow = getWindowByGoalId(pretty.windows, nextGoal.id);
      }

      return;
    // - we updated the goal!
    } else if (relevantGoalsAfter.length === 1) { 
      const updatedGoal = relevantGoalsAfter[0];
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
    // - we forked the goal!
    } else {
      prettyGoalArrows = relevantGoalsAfter.map((goal) => ({
        fromId: mainGoalBefore.id,
        toId: goal.id
      }));

      // We are creating new child windows
      const childWindows = relevantGoalsAfter.map((goal) => ({
        id: ++newId,
        parentId: currentWindow.id,
        goalNodes: [
          {
            text: goal.type,
            id: goal.id
          }
        ],
        hypNodes: []
      }));
      pretty.windows.push(...childWindows)
      // We are moving into the first of child windows
      currentWindow = childWindows[0];

      // Sometimes, when we fork the goal, we update other goals' hypotheses too!
      // For example, `cases (h: P ∨ Q)` would do this.
      // So - the tactic always works on the current goal; with one exception for when it forks the goals.
      // So we should call "4. Draw the hypotheses!" per each goal.
      // TODO
      // Per each (childGoal, index):
      // 1. find its newly created window
      // 2. in that window, draw hypotheses
      // TODO
      relevantGoalsAfter.forEach((goalAfter, index) => {
        // We don't need to do this for the current window - we'll do this below.
        if (index === 0) return;

        const hypsBefore = mainGoalBefore.hyps;
        const hypsAfter  = goalAfter.hyps;
        let [prettyHypNodes, prettyHypArrows] = drawNewHypotheses(hypsBefore, hypsAfter);

        if (prettyHypNodes.length > 0) {
          const childWindow = getWindowByGoalId(pretty.windows, goalAfter.id);
          childWindow.hypNodes.push(prettyHypNodes);
        }
      });
    }

    const hypsBefore = tactic.goalsBefore[0].hyps;
    const hypsAfter  = tactic.goalsAfter[0].hyps;
    let [prettyHypNodes, prettyHypArrows] = drawNewHypotheses(hypsBefore, hypsAfter);

    if (prettyHypNodes.length > 0) {
      currentWindow.hypNodes.push(prettyHypNodes);
    }

    pretty.tactics.push({
      text         : tactic.tacticString,
      dependsOnIds : tactic.tacticDependsOn,
      goalArrows   : prettyGoalArrows,
      hypArrows    : prettyHypArrows,
      // success arrows are better not drawn (noisy!), we should just mark the tactic as 🎉.
      // dependsOnIds will convey all the information we want to see.
      isSuccess    : false
    });
    // TODO write what goal it closes
  })

  return pretty
}


const edges = toEdges(infoTreeExample)
console.log(util.inspect(edges, { depth: null }));
