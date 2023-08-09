import { Editor, TLShapeId, createShapeId } from '@tldraw/tldraw';

import buildProofTree from './buildProofTree';
import focusProofTree from './focusProofTree';
import zoomToWindow from './zoomToWindow';

import { ProofResponse } from '../types';
import CreateId from './buildProofTree/services/CreateId';

const uiConfig = {
  // Ideally it should be `hideNonContributingHyps` to hide all hyps which aren't contributing to goals in any way, but determining what hyps are used in what tactics isn't implemented properly yet, e.g. in linarith.
  hideNulls: true,
};

const areObjectsEqual = (a: object, b: object) => {
  return JSON.stringify(a) === JSON.stringify(b);
};

const zoomProofTree = (editor: Editor) => {
  const previouslyFocusedWindow = window.zoomedWindowId && editor.getShape(window.zoomedWindowId);
  const rootWindow = editor.getShape(CreateId.window(1));
  const desiredWindow = previouslyFocusedWindow || rootWindow;
  if (desiredWindow) {
    zoomToWindow(editor, desiredWindow);
  }
}

const updateUI = (editor: Editor, oldProof: ProofResponse, newProof: ProofResponse) => {
  editor.updateInstanceState({ isReadonly: false });
  console.info({ oldProof, newProof });

  const isNewProofEmpty = !newProof || "error" in newProof;
  const isOldProofEmpty = !oldProof || "error" in oldProof;

  if (isNewProofEmpty) {
    editor.deleteShapes(editor.currentPageShapes);
    return;
  }

  if (isOldProofEmpty || !areObjectsEqual(newProof.proofTree, oldProof.proofTree)) {
    console.info("buildProofTree");
    buildProofTree(editor, newProof.proofTree, uiConfig);
    // Frequently, the goal arrives in the previous updateUI!
    // TODO investigate why that is, and update this code accordingly.
    focusProofTree(editor, newProof.proofTree.equivalentIds, newProof.goal);
  }
  if (isOldProofEmpty || !areObjectsEqual(newProof.goal, oldProof.goal)) {
    console.info("focusProofTree");
    focusProofTree(editor, newProof.proofTree.equivalentIds, newProof.goal);
  }
  if (isOldProofEmpty || newProof.statement !== oldProof.statement) {
    console.info("zoomProofTree");
    zoomProofTree(editor);
  }
  editor.updateInstanceState({ isReadonly: true });
}

export default updateUI;
