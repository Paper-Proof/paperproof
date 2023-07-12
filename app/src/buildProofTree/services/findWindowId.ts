import { App, TLShapeId } from "@tldraw/tldraw";
import findIdInApp from './findIdInApp';
import { Format } from "../../types";

import { createWindowId } from './CreateId';

const findWindowId = (app: App, proofTree: Format, goalId: string): TLShapeId | null => {
  const window = proofTree.windows.find((window) =>
    window.goalNodes.find((goalNode) => goalNode.id === goalId)
  );
  if (window) {
    return findIdInApp(app, createWindowId(app, window.id));
  } else {
    return null;
  }
}

export default findWindowId;
