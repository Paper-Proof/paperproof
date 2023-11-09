import { Editor } from "@tldraw/tldraw";
import { ConvertedProofTree, UIConfig } from "types";
import { createWindow, createArrows } from './services/CreateElement';
import createDependsOnArrows from "./services/CreateElement/createDependsOnArrows";

const buildProofTree = (editor: Editor, proofTree: ConvertedProofTree, uiConfig: UIConfig) => {
  editor.deleteShapes(editor.currentPageShapes);

  const shared = {
    editor: editor,
    uiConfig,
    proofTree,
    inBetweenMargin: 20,
    framePadding: 20
  };

  const root = proofTree.boxes.find((w) => w.parentId == null);
  if (root) {
    const rootWindow = createWindow(shared, undefined, root, 0);
    rootWindow.draw(0, 0);

    const arrows = createArrows(shared);
    arrows.draw(0, 0);

    const dependsOnArrows = createDependsOnArrows(shared);
    dependsOnArrows.draw(0, 0);

    // Would be nice to hide the arrows behind arrows, but that doesn't work here. Didn't investigate why.
    //
    // const shapes = shared.editor.currentPageShapes.filter((shape) => shape.type === "customNode")
    // shared.editor.bringToFront(shapes)
  }
}

export default buildProofTree;
