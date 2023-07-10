import { Shared, Element } from "../../../types";

import { drawShapeArrow } from '../DrawShape';

import findIdInApp from '../findIdInApp';
import findWindowId from '../findWindowId'

const createArrows = (shared: Shared): Element => {
  return {
    size: [0, 0],
    draw: (x: number, y: number) => {
      // TODO:lakesare put id creation in a separate file & reuse it in Creator.ts
      shared.proofTree.tactics.forEach((tactic) => {
        tactic.hypArrows.forEach((hypArrow) => {
          if (hypArrow.fromId) {
            const fromNodeId = findIdInApp(shared.app, hypArrow.fromId);
            const toTacticId = findIdInApp(shared.app, `tactic-${tactic.id}-${hypArrow.fromId}`);
            if (!fromNodeId || !toTacticId) return
            drawShapeArrow(shared.app, fromNodeId, toTacticId);
          }
          hypArrow.toIds.forEach((toId) => {
            const fromTacticId = findIdInApp(shared.app, `tactic-${tactic.id}-${hypArrow.fromId}`);
            const toNodeId = findIdInApp(shared.app, toId);
            if (!fromTacticId || !toNodeId) return
            drawShapeArrow(shared.app, fromTacticId, toNodeId);
          });
        });

        tactic.goalArrows.forEach((goalArrow) => {
          const tacticId = findIdInApp(shared.app, `${tactic.id}`);
          const toNodeId = findIdInApp(shared.app, goalArrow.fromId);
          const fromNodeId = findIdInApp(shared.app, goalArrow.toId);

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

        if (tactic.haveWindowId) {
          const fromWindowId = findIdInApp(shared.app, `window-${tactic.haveWindowId}`);
          const toTacticId = findIdInApp(shared.app, `tactic-${tactic.id}-null`);
          if (!fromWindowId || !toTacticId) return
          drawShapeArrow(shared.app, fromWindowId, toTacticId);
        }
      });
    }
  };
}

export default createArrows;
