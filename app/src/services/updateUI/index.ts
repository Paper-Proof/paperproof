import { ProofResponse, UIConfig } from 'types';
import { Editor } from '@tldraw/tldraw';
import buildProofTree     from './services/buildProofTree';
import highlightProofTree from './services/highlightProofTree';
import zoomProofTree      from './services/zoomProofTree';
import converter from './services/converter';
import getStatement     from './services/getStatement';
import areObjectsEqual  from '../../library/areObjectsEqual';
import getLoggableProof from './services/getLoggableProof';

let lastValidStatement: string | null;

const updateUI = (editor: Editor, oldProof: ProofResponse, newProof: ProofResponse, uiConfig: UIConfig) => {
  editor.updateInstanceState({ isReadonly: false });

  // console.table({ oldProof: getLoggableProof(oldProof), newProof: getLoggableProof(newProof) });

  const isNewProofEmpty = !newProof || "error" in newProof;
  const isOldProofEmpty = !oldProof || "error" in oldProof;

  if (isNewProofEmpty) {
    if (!newProof) {
      return;
    }
    if (newProof.error === 'File changed.' || newProof.error === 'stillTyping' || newProof.error === 'leanNotYetRunning') {
      return;
    } else if (newProof.error === 'zeroProofSteps') {
      // editor.deleteShapes(editor.currentPageShapes);
      return;
    } else {
      console.warn("We are not explicitly handling some error?");
      console.warn(newProof);
      return;
    }
  }

  // Delete stored zoomedWindowId if we switched the theorems.
  if (lastValidStatement !== getStatement(newProof.proofTree)) {
    localStorage.removeItem('zoomedWindowId');
    lastValidStatement = getStatement(newProof.proofTree);
  }

  // Every time user clicks on something, we build/highlight/zoom the tree anew!
  const newProofTree = converter(newProof.proofTree);
  // The only expensive operation here is building the proof tree, so we try not to do it unless it's necessary
  if (isOldProofEmpty || !areObjectsEqual(oldProof.proofTree, newProof.proofTree)) {
    buildProofTree(editor, newProofTree, uiConfig);
  }
  highlightProofTree(editor, newProofTree.equivalentIds, newProof.goal);
  zoomProofTree(editor, newProofTree, newProof.goal?.mvarId);

  editor.updateInstanceState({ isReadonly: true });
}

export default updateUI;
