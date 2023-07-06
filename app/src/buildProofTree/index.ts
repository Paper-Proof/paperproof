import { App, TLShapeId } from "@tldraw/tldraw";
import { Format, UiConfig } from "../types";
import { createWindow } from './services/Creator';
import { drawShapeArrow } from './services/drawShape';

const findIdInApp = (app: App, id: string): TLShapeId | null => {
  const desiredId = app.createShapeId(id);
  const existingShapeIds = Array.from(app.shapeIds.values());
  console.log(`Searching for ${id} in:`);
  console.log(existingShapeIds);
  const foundId = existingShapeIds.find((shapeId) => shapeId === desiredId)
  if (foundId) {
    console.log(`Found: ${foundId}`)
    return foundId;
  }

  console.log("Didn't find");
  return null
}

const findWindowId = (app : App, proofTree : Format, goalId : string) : TLShapeId | null => {
  const window = proofTree.windows.find((window) =>
    window.goalNodes.find((goalNode) => goalNode.id === goalId)
  )
  if (window) {
    return findIdInApp(app, `window-${window.id}`);
  } else {
    return null;
  }
}

export function buildProofTree(app: App, proofTree: Format, currentGoal: string, uiConfig: UiConfig) {
  app.selectAll().deleteShapes();
  app.updateInstanceState({ isFocusMode: true });

  const shared = {
    app,
    uiConfig,
    proofTree,
    currentGoal
  };

  const root = proofTree.windows.find((w) => w.parentId == null);
  if (root) {
    const el = createWindow(shared, undefined, root, 0);
    el.draw(0, 0);

    // TODO:lakesare put id creation in a separate file & reuse it in Creator.ts
    // TODO:lakesare move this somewhere
    proofTree.tactics.forEach((tactic) => {
      tactic.hypArrows.forEach((hypArrow) => {
        if (hypArrow.fromId) {
          const fromNodeId = findIdInApp(app, hypArrow.fromId);
          const toTacticId = findIdInApp(app, `tactic-${tactic.id}-${hypArrow.fromId}`);
          if (!fromNodeId || !toTacticId) return
          drawShapeArrow(app, fromNodeId, toTacticId);
        }
        hypArrow.toIds.forEach((toId) => {
          const fromTacticId = findIdInApp(app, `tactic-${tactic.id}-${hypArrow.fromId}`);
          const toNodeId = findIdInApp(app, toId);
          if (!fromTacticId || !toNodeId) return
          drawShapeArrow(app, fromTacticId, toNodeId);
        });
      });

      tactic.goalArrows.forEach((goalArrow) => {
        const tacticId = findIdInApp(app, `${tactic.id}`);
        const toNodeId = findIdInApp(app, goalArrow.fromId);
        const fromNodeId = findIdInApp(app, goalArrow.toId);
        
        const windowId1 = findWindowId(app, proofTree, goalArrow.fromId);
        const windowId2 = findWindowId(app, proofTree, goalArrow.toId);
        if (!tacticId || !toNodeId || !fromNodeId || !windowId1 || !windowId2) return
        if (windowId1 === windowId2) {
          drawShapeArrow(app, fromNodeId, tacticId);
        } else {
          drawShapeArrow(app, windowId2, tacticId);
        }

        drawShapeArrow(app, tacticId, toNodeId);
      });

      if (tactic.haveWindowId) {
        const fromWindowId = findIdInApp(app, `window-${tactic.haveWindowId}`);
        const toTacticId = findIdInApp(app, `tactic-${tactic.id}-null`);
        if (!fromWindowId || !toTacticId) return
        drawShapeArrow(app, fromWindowId, toTacticId);
      }
    });
  }
}
