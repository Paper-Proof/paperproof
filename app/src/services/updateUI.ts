import { Editor } from '@tldraw/tldraw';

import buildProofTree from './buildProofTree';
import highlightNodes from './highlightNodes';
import zoomProofTree from './zoomProofTree';

import { LeanGoal, LeanProofTree, ProofResponse } from 'types';

import converter from '../converter';

const uiConfig = {
  // Ideally it should be `hideNonContributingHyps` to hide all hyps which aren't contributing to goals in any way, but determining what hyps are used in what tactics isn't implemented properly yet, e.g. in linarith.
  hideNulls: true,
};

const areObjectsEqual = (a: object, b: object) => {
  return JSON.stringify(a) === JSON.stringify(b);
};

const getInitialGoal = (subSteps: LeanProofTree): string | null => {
  const firstStep = subSteps[0];
  if ('tacticApp' in firstStep) {
    return firstStep.tacticApp.t.goalsBefore[0].type;
  } else if ('haveDecl' in firstStep) {
    return firstStep.haveDecl.t.goalsBefore[0].type;
  }
  return null;
}

// This is resource-heavy, one of the reasons we want a production build that strips console.logs
const loggableProof = (proof: ProofResponse) => {
  if (!proof) {
    return null;
  } else if ("error" in proof) {
    return proof;
  } else {
    return converter(proof.proofTree);
  }
}

let lastValidStatement : string | null;

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

  // Delete stored zoomedWindowId if we switched the theorems.
  if (lastValidStatement !== getInitialGoal(newProof.proofTree)) {
    localStorage.removeItem('zoomedWindowId');
    lastValidStatement = getInitialGoal(newProof.proofTree);
  }

  // Every time user clicks on something, we build/highlight/zoom the tree anew!
  const newProofTree = converter(newProof.proofTree);
  // The only expensive operation here is building the proof tree, so we try not to do it unless it's necessary
  if (isOldProofEmpty || !areObjectsEqual(oldProof.proofTree, newProof.proofTree)) {
    buildProofTree(editor, newProofTree, uiConfig);
  }
  highlightNodes(editor, newProofTree.equivalentIds, newProof.goal);
  zoomProofTree(editor, newProofTree, newProof.goal?.mvarId);

  editor.updateInstanceState({ isReadonly: true });
}

export default updateUI;
