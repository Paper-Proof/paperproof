import { Shared, Element } from "../../../../types";
import DrawShape from '../DrawShape';
import { Format } from "../../../../types";
import CreateId from '../CreateId';
import { Editor as App, TLShapeId } from "@tldraw/tldraw";

const findIdInApp = (app: App, desiredId: TLShapeId): TLShapeId | null => {
  const existingShapeIds = app.currentPageShapes;
  const desiredShape = app.getShape(desiredId);

  if (desiredShape) {
    return desiredShape.id;
  } else {
    console.log(`Didn't find ${desiredId} in:`);
    console.log(existingShapeIds);
    return null
  }
}

const getWindowByHypId = (proofTree: Format, hypId : string) =>
  proofTree.windows.find((window) =>
    window.hypNodes.find((hypLayer) => hypLayer.find((hyp) => hyp.id === hypId))
  );

const findWindowId = (app: App, proofTree: Format, goalId: string): TLShapeId | null => {
  const window = proofTree.windows.find((window) =>
    window.goalNodes.find((goalNode) => goalNode.id === goalId)
  );
  if (window) {
    return findIdInApp(app, CreateId.window(app, window.id));
  } else {
    return null;
  }
}

const createArrows = (shared: Shared): Element => {
  return {
    size: [0, 0],
    draw: (x: number, y: number) => {
      shared.proofTree.tactics.forEach((tactic) => {
        // 1. Draw arrows between this tactic and hypotheses
        tactic.hypArrows.forEach((hypArrow) => {
          hypArrow.toIds.forEach((toId) => {
            const window = getWindowByHypId(shared.proofTree, toId);
            if (!window) return

            if (hypArrow.fromId) {
              const fromNodeId = findIdInApp(shared.app, CreateId.node(shared.app, hypArrow.fromId));
              const toTacticId = findIdInApp(shared.app, CreateId.hypTactic(shared.app, tactic.id, hypArrow.fromId, window.id));
              if (!fromNodeId || !toTacticId) return
              DrawShape.arrow(shared.app, fromNodeId, toTacticId);
            }
            const fromTacticId = findIdInApp(shared.app, CreateId.hypTactic(shared.app, tactic.id, hypArrow.fromId, window.id));
            const toNodeId = findIdInApp(shared.app, CreateId.node(shared.app, toId));
            if (!fromTacticId || !toNodeId) return
            DrawShape.arrow(shared.app, fromTacticId, toNodeId);
          });
        });

        // 2. Draw arrows between this tactic and goals
        tactic.goalArrows.forEach((goalArrow) => {
          const tacticId = findIdInApp(shared.app, CreateId.goalTactic(shared.app, tactic.id));
          const toNodeId = findIdInApp(shared.app, CreateId.node(shared.app, goalArrow.fromId));
          const fromNodeId = findIdInApp(shared.app, CreateId.node(shared.app, goalArrow.toId));

          const windowId1 = findWindowId(shared.app, shared.proofTree, goalArrow.fromId);
          const windowId2 = findWindowId(shared.app, shared.proofTree, goalArrow.toId);
          if (!tacticId || !toNodeId || !fromNodeId || !windowId1 || !windowId2) return
          if (windowId1 === windowId2) {
            DrawShape.arrow(shared.app, fromNodeId, tacticId);
          } else {
            DrawShape.arrow(shared.app, windowId2, tacticId);
          }

          DrawShape.arrow(shared.app, tacticId, toNodeId);
        });

        // 3. Draw arrows between this tactic and `have` windows
        if (tactic.haveWindowId && tactic.hypArrows[0]) {
          const window = getWindowByHypId(shared.proofTree, tactic.hypArrows[0].toIds[0]);
          if (!window) return
          const fromWindowId = findIdInApp(shared.app, CreateId.window(shared.app, tactic.haveWindowId));
          const toTacticId = findIdInApp(shared.app, CreateId.hypTactic(shared.app, tactic.id, null, window.id));
          if (!fromWindowId || !toTacticId) return
          DrawShape.arrow(shared.app, fromWindowId, toTacticId);
        }
      });
    }
  };
}

export default createArrows;
