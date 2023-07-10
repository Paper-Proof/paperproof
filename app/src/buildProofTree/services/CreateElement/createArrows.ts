import { Shared, Element } from "../../../types";

import { drawShapeArrow } from '../DrawShape';

import findIdInApp from '../findIdInApp';
import findWindowId from '../findWindowId'

import { createHypTacticId, createGoalTacticId, createNodeId, createWindowId } from '../CreateId';

const createArrows = (shared: Shared): Element => {
  return {
    size: [0, 0],
    draw: (x: number, y: number) => {
      shared.proofTree.tactics.forEach((tactic) => {
        // 1. Draw arrows between this tactic and hypotheses
        tactic.hypArrows.forEach((hypArrow) => {
          if (hypArrow.fromId) {
            const fromNodeId = findIdInApp(shared.app, createNodeId(shared.app, hypArrow.fromId));
            const toTacticId = findIdInApp(shared.app, createHypTacticId(shared.app, tactic.id, hypArrow.fromId));
            if (!fromNodeId || !toTacticId) return
            drawShapeArrow(shared.app, fromNodeId, toTacticId);
          }
          hypArrow.toIds.forEach((toId) => {
            const fromTacticId = findIdInApp(shared.app, createHypTacticId(shared.app, tactic.id, hypArrow.fromId));
            const toNodeId = findIdInApp(shared.app, createNodeId(shared.app, toId));
            if (!fromTacticId || !toNodeId) return
            drawShapeArrow(shared.app, fromTacticId, toNodeId);
          });
        });

        // 2. Draw arrows between this tactic and goals
        tactic.goalArrows.forEach((goalArrow) => {
          const tacticId = findIdInApp(shared.app, createGoalTacticId(shared.app, tactic.id));
          const toNodeId = findIdInApp(shared.app, createNodeId(shared.app, goalArrow.fromId));
          const fromNodeId = findIdInApp(shared.app, createNodeId(shared.app, goalArrow.toId));

          const windowId1 = findWindowId(shared.app, shared.proofTree, goalArrow.fromId);
          const windowId2 = findWindowId(shared.app, shared.proofTree, goalArrow.toId);
          if (!tacticId || !toNodeId || !fromNodeId || !windowId1 || !windowId2) return
          if (windowId1 === windowId2) {
            drawShapeArrow(shared.app, fromNodeId, tacticId);
          } else {
            drawShapeArrow(shared.app, windowId2, tacticId);
          }

          drawShapeArrow(shared.app, tacticId, toNodeId);
        });

        // 3. Draw arrows between this tactic and `have` windows
        if (tactic.haveWindowId) {
          const fromWindowId = findIdInApp(shared.app, createWindowId(shared.app, tactic.haveWindowId));
          const toTacticId = findIdInApp(shared.app, createHypTacticId(shared.app, tactic.id, null));
          if (!fromWindowId || !toTacticId) return
          drawShapeArrow(shared.app, fromWindowId, toTacticId);
        }
      });
    }
  };
}

export default createArrows;
