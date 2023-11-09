import { Editor } from '@tldraw/tldraw';
import CreateId from './buildProofTree/services/CreateId';
import zoomToWindow from '../../../library/zoomToWindow';
import getDisplayedId from 'src/services/updateUI/services/getDisplayedId';
import { ConvertedProofTree, Box } from 'types';

const getParentWindowId = (windows: Box[], childId: string): string | null => {
  const childWindow = windows.find((w) => w.id === childId);
  const parentId = childWindow!.parentId;
  return parentId;
}

const findLcm = (windows: Box[], windowIdA: string, windowIdB: string): string => {
  const parentsOfA: (string | null)[] = [];
  let idA: string | null = windowIdA;
  while (true) {
    parentsOfA.push(idA);
    if (idA === null) { break; }
    idA = getParentWindowId(windows, idA);
  }

  let idB: string | null = windowIdB;
  while (true) {
    // Shouldn't ever happen, it's only here to calm typescript
    if (idB === null) { return windowIdB; }
    // We found our lowest shared parent!
    if (parentsOfA.includes(idB)) {
      return idB;
    }
    idB = getParentWindowId(windows, idB);
  }
}

const zoomProofTree = (editor: Editor, convertedTree: ConvertedProofTree, goalId: string | undefined) => {
  // This is necessary, if we don't do this zooming will work stupidly until we click on the webview tab (this line makes `editor.viewportScreenBounds` correct).
  editor.updateViewportScreenBounds();
  
  // 1. If there is no interactive goal, then we're on the last line, so rezoom on root.
  // 2. If the user never clicked on any window - then rezoom on root.
  const lastClickedOnWindowId = localStorage.getItem('zoomedWindowId')
  const lastClickedOnWindow = lastClickedOnWindowId && editor.getShape(CreateId.window(lastClickedOnWindowId));
  if (!goalId || !lastClickedOnWindow) {
    const rootWindow = editor.getShape(CreateId.window("1"));
    if (rootWindow) {
      zoomToWindow(editor, rootWindow);
    }
    return;
  }

  // 3. Rezoom on the common ancestor of (windowWithCurrentGoal, lastClickedOnWindowId)
  const windowWithCurrentGoal = convertedTree.boxes.find((w) =>
    w.goalNodes.find((g) => g.id === getDisplayedId(convertedTree.equivalentIds, goalId))
  );
  if (!windowWithCurrentGoal) {
    console.error(`We tried to zoom in, but couldn't find the window with the goal ${goalId}. This probably shouldn't happen, check what went wrong.`);
    return;
  }

  let lcmWindowId = findLcm(convertedTree.boxes, windowWithCurrentGoal.id, lastClickedOnWindowId);
  const lcmWindow = editor.getShape(CreateId.window(lcmWindowId));

  if (lcmWindow) {
    zoomToWindow(editor, lcmWindow);
  }
}

export default zoomProofTree;
