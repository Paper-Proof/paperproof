import { Editor } from "@tldraw/tldraw";
import { Format, UiConfig } from "../../types";
import { createWindow, createArrows } from './services/CreateElement';

const buildProofTree = (editor: Editor, proofTree: Format, uiConfig: UiConfig) => {
  editor.deleteShapes(editor.currentPageShapes);

  const shared = {
    editor: editor,
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

export default buildProofTree;
