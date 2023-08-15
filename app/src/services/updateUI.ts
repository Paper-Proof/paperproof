import { Editor, TLShapeId, createShapeId } from '@tldraw/tldraw';

import buildProofTree from './buildProofTree';
import highlightNodes from './highlightNodes';
import zoomToWindow from './zoomToWindow';

import { ProofResponse } from '../types';
import CreateId from './buildProofTree/services/CreateId';

import converter from '../converter';

const uiConfig = {
  // Ideally it should be `hideNonContributingHyps` to hide all hyps which aren't contributing to goals in any way, but determining what hyps are used in what tactics isn't implemented properly yet, e.g. in linarith.
  hideNulls: true,
};

const areObjectsEqual = (a: object, b: object) => {
  return JSON.stringify(a) === JSON.stringify(b);
};

const zoomProofTree = (editor: Editor) => {
  // This is necessary, if we don't do this zooming will work stupidly until we click on the webview tab (this makes `editor.viewportScreenBounds` correct).
  editor.updateViewportScreenBounds();

  const previouslyFocusedWindow = window.zoomedWindowId && editor.getShape(window.zoomedWindowId);
  const rootWindow = editor.getShape(CreateId.window(1));

  const desiredWindow = previouslyFocusedWindow || rootWindow;
  if (desiredWindow) {
    zoomToWindow(editor, desiredWindow);
  }
}

// lakesare: not finished, this is a step towards proof blinking debugging
const loggableProof = (proof: ProofResponse) => {
  if (!proof) {
    return null;
  } else if ("error" in proof) {
    return proof;
  } else {
    return converter(proof.proofTree);
  }
}

const updateUI = (editor: Editor, oldProof: ProofResponse, newProof: ProofResponse) => {
  editor.updateInstanceState({ isReadonly: false });

  console.table({ oldProof: loggableProof(oldProof), newProof: loggableProof(newProof) });

  const isNewProofEmpty = !newProof || "error" in newProof;
  const isOldProofEmpty = !oldProof || "error" in oldProof;

  if (isNewProofEmpty) {
    if (!newProof) {
      return;
    }
    if (newProof.error === 'File changed.' || newProof.error === 'stillTyping' || newProof.error === 'leanNotYetRunning') {
      return;
    } else if (newProof.error === 'zeroProofSteps') {
      editor.deleteShapes(editor.currentPageShapes);
      return;
    } else {
      console.warn("We are not explicitly handling some error?");
      console.warn(newProof);
      return;
    }
  }

  // if (isOldProofEmpty || !areObjectsEqual(newProof.proofTree, oldProof.proofTree)) {
  //   const newProofTree = converter(newProof.proofTree);
  //   buildProofTree(editor, newProofTree, uiConfig);
  //   // Frequently, the goal arrives in the previous updateUI!
  //   // TODO investigate why that is, and update this code accordingly.
  //   highlightNodes(editor, newProofTree.equivalentIds, newProof.goal);
  // }
  // if (isOldProofEmpty || !areObjectsEqual(newProof.goal, oldProof.goal)) {
  //   const newProofTree = converter(newProof.proofTree);
  //   highlightNodes(editor, newProofTree.equivalentIds, newProof.goal);
  // }
  // if (isOldProofEmpty || newProof.statement !== oldProof.statement) {
  //   zoomProofTree(editor);
  // }

  // So just - every time editor selection is changed, we do everything!
  const newProofTree = converter(newProof.proofTree);
  buildProofTree(editor, newProofTree, uiConfig);
  highlightNodes(editor, newProofTree.equivalentIds, newProof.goal);
  zoomProofTree(editor);

  editor.updateInstanceState({ isReadonly: true });
}

export default updateUI;
