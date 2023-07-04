import { App, TLShapeId } from "@tldraw/tldraw";
import { HypNode, Format, UiConfig } from "../types";
import { createWindow } from './services/Creator';

export function buildProofTree(app: App, proofTree: Format, currentGoal: string, uiConfig: UiConfig) {
  app.selectAll().deleteShapes();
  app.updateInstanceState({ isFocusMode: true });

  const shapeMap = new Map<string, TLShapeId>();

  function drawArrow(from: TLShapeId, to: TLShapeId) {
    app.createShapes([
      {
        id: app.createShapeId(),
        type: "customArrow",
        props: {
          start: {
            type: 'binding', boundShapeId: from,
            normalizedAnchor: { x: 0.5, y: 1 },
            isExact: true
          },
          end: {
            type: 'binding', boundShapeId: to,
            normalizedAnchor: { x: 0.5, y: 0 },
            isExact: true
          },
          color: "grey",
        },
      },
    ]);
  }

  const arrowsToDraw: ({ fromId: string, toShapeId: TLShapeId } | { fromShapeId: TLShapeId, toId: string })[] = [];

  const shared = {
    app,
    uiConfig,
    arrowsToDraw,
    proofTree,
    shapeMap,
    currentGoal
  }

  const root = proofTree.windows.find((w) => w.parentId == null);
  if (root) {
    const el = createWindow(shared, undefined, root, 0);
    el.draw(0, 0);
  }
  // Draw arrows
  for (const arrow of arrowsToDraw) {
    if ('fromId' in arrow) {
      const fromShapeId = shapeMap.get(arrow.fromId);
      if (fromShapeId) {
        drawArrow(fromShapeId, arrow.toShapeId)
      }
    } else {
      const toShapeId = shapeMap.get(arrow.toId);
      if (toShapeId) {
        drawArrow(arrow.fromShapeId, toShapeId);
      }
    }
  }
}
