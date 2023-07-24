import { Editor as App } from "@tldraw/tldraw";
import { Format, UiConfig } from "../types";
import { createWindow, createArrows } from './services/CreateElement';

export function buildProofTree(app: App, proofTree: Format, uiConfig: UiConfig) {
  app.selectAll().deleteShapes();

  const shared = {
    app,
    uiConfig,
    proofTree,
    inBetweenMargin: 20,
    framePadding: 20
  };

  const root = proofTree.windows.find((w) => w.parentId == null);
  if (root) {
    const rootWindow = createWindow(shared, undefined, root, 0);
    rootWindow.draw(0, 0);

    const arrows = createArrows(shared);
    arrows.draw(0, 0);
  }
}
