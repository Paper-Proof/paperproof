import { App, TLShapeId } from "@tldraw/tldraw";
import { Format, UiConfig } from "../types";
import { createWindow } from './services/Creator';
import { drawShapeArrow } from './services/drawShape';

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
      drawShapeArrow(app, arrow.fromId, arrow.toId);
    }
  }
}
