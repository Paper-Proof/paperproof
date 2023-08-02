import { Editor, createShapeId } from '@tldraw/tldraw';

import buildProofTree from './buildProofTree';
import focusProofTree from './focusProofTree';
import zoomToWindow from './zoomToWindow';

import { ProofResponse } from '../types';

const uiConfig = {
  // Ideally it should be `hideNonContributingHyps` to hide all hyps which aren't contributing to goals in any way, but determining what hyps are used in what tactics isn't implemented properly yet, e.g. in linarith.
  hideNulls: true,
};

const areObjectsEqual = (a: object, b: object) => {
  return JSON.stringify(a) === JSON.stringify(b);
};

const zoomProofTree = (editor: Editor) => {
  const window = editor.getShape(createShapeId("window-1"));
  if (window) {
    zoomToWindow(editor, window);
  }
}

const updateUI = (editor: Editor, oldProof: ProofResponse, newProof: ProofResponse) => {
  const isNewProofEmpty = !newProof || "error" in newProof;
  const isOldProofEmpty = !oldProof || "error" in oldProof;

  if (isNewProofEmpty) {
    const shapes = Array.from(editor.getPageShapeIds(editor.currentPageId));
    editor.deleteShapes(shapes);
    return;
  }

  if (isOldProofEmpty || !areObjectsEqual(newProof.proofTree, oldProof.proofTree)) {
    buildProofTree(editor, newProof.proofTree, uiConfig);
  }
  if (isOldProofEmpty || !areObjectsEqual(newProof.goal, oldProof.goal)) {
    focusProofTree(editor, newProof.proofTree.equivalentIds, newProof.goal);
  }
  if (isOldProofEmpty || newProof.statement !== oldProof.statement) {
    zoomProofTree(editor);
  }
}

export default updateUI;
