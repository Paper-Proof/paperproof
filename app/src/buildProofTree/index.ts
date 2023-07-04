import { App, TLShapeId } from "@tldraw/tldraw";
import { Format, UiConfig } from "../types";
import { createWindow } from './services/Creator';

function drawArrow(app: App, fromId: TLShapeId, toId: TLShapeId) {
  app.createShapes([
    {
      id: app.createShapeId(),
      type: "customArrow",
      props: {
        start: {
          type: 'binding', boundShapeId: fromId,
          normalizedAnchor: { x: 0.5, y: 1 },
          isExact: true
        },
        end: {
          type: 'binding', boundShapeId: toId,
          normalizedAnchor: { x: 0.5, y: 0 },
          isExact: true
        },
        color: "grey",
      },
    },
  ]);
}

export function buildProofTree(app: App, proofTree: Format, currentGoal: string, uiConfig: UiConfig) {
  app.selectAll().deleteShapes();
  app.updateInstanceState({ isFocusMode: true });

  const arrowsToDraw: ({ fromId: TLShapeId, toId: TLShapeId })[] = [];

  const shared = {
    app,
    uiConfig,
    arrowsToDraw,
    proofTree,
    currentGoal
  }

  const root = proofTree.windows.find((w) => w.parentId == null);
  if (root) {
    const el = createWindow(shared, undefined, root, 0);
    el.draw(0, 0);
    for (const arrow of arrowsToDraw) {
      drawArrow(app, arrow.fromId, arrow.toId);
    }
  }
}
