import { Editor as App, createShapeId } from '@tldraw/tldraw';

import buildProofTree from './buildProofTree';
import focusProofTree from './focusProofTree';
import zoomToWindow from './zoomToWindow';

import { ProofResponse } from '../types';

const uiConfig = {
  // Ideally it should be `hideNonContributingHyps` to hide all hyps which aren't contributing
  // to goals in any way, but determining what hyps are used in what tactics isn't implemented
  // properly yet, e.g. in linarith.
  hideNulls: true,
};

const areObjectsEqual = (a: object, b: object) => {
  return JSON.stringify(a) === JSON.stringify(b);
};

const zoomProofTree = (app: App) => {
  const window = app.getShape(createShapeId("window-1"));
  if (window) {
    zoomToWindow(app, window);
  }
}

const updateUI = (app: App, oldProof: ProofResponse, newProof: ProofResponse) => {
  const isNewProofEmpty = !newProof || "error" in newProof;
  const isOldProofEmpty = !oldProof || "error" in oldProof;

  if (isNewProofEmpty) {
    const shapes = Array.from(app.getPageShapeIds(app.currentPageId));
    app.deleteShapes(shapes);
    return;
  }

  if (isOldProofEmpty || !areObjectsEqual(newProof.proofTree, oldProof.proofTree)) {
    buildProofTree(app, newProof.proofTree, uiConfig);
  }
  if (isOldProofEmpty || !areObjectsEqual(newProof.goal, oldProof.goal)) {
    focusProofTree(app, newProof.proofTree.equivalentIds, newProof.goal);
  }
  if (isOldProofEmpty || newProof.statement !== oldProof.statement) {
    zoomProofTree(app);
  }
}

export default updateUI;
