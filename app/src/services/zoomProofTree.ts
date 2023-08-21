import { Editor } from '@tldraw/tldraw';
import CreateId from './buildProofTree/services/CreateId';
import zoomToWindow from './zoomToWindow';
import { Format, Window } from 'src/types';
import getDisplayedId from 'src/shared/getDisplayedId';

// temporary, TODO
declare const window: any;

const getParentWindowId = (windows: Window[], childId: number): number | null => {
  const childWindow = windows.find((w) => w.id === childId);
  const parentId = childWindow!.parentId;
  return parentId;
}

const findLcm = (windows: Window[], windowIdA: number, windowIdB: number): number => {
  const parentsOfA: (number | null)[] = [];
  let idA: number | null = windowIdA;
  while (true) {
    parentsOfA.push(idA);
    if (idA === null) { break; }
    idA = getParentWindowId(windows, idA);
  }

  let idB: number | null = windowIdB;
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

const zoomProofTree = (editor: Editor, convertedTree: Format, goalId: string | undefined) => {
  // This is necessary, if we don't do this zooming will work stupidly until we click on the webview tab (this line makes `editor.viewportScreenBounds` correct).
  editor.updateViewportScreenBounds();

  let desiredWindowId : number;

  const previouslyFocusedWindow = window.zoomedWindowId && editor.getShape(window.zoomedWindowId);

  if (previouslyFocusedWindow) {
    // lol TODO
    // this should probably be metadata instead
    desiredWindowId = Number(window.zoomedWindowId.split("shape:window-")[1]);
  } else {
    desiredWindowId = 1;
  }

  // zoom to root!
  if (!goalId) {
    const desiredWindow = editor.getShape(CreateId.window(1));
    if (desiredWindow) {
      zoomToWindow(editor, desiredWindow);
    }
    return;
  }

  const windowWithCurrentGoal = convertedTree.windows.find((w) =>
    w.goalNodes.find((g) => g.id === getDisplayedId(convertedTree.equivalentIds, goalId))
  );
  let lcmWindowId = findLcm(convertedTree.windows, windowWithCurrentGoal!.id, desiredWindowId);

  const lcmWindow = editor.getShape(CreateId.window(lcmWindowId));

  if (lcmWindow) {
    zoomToWindow(editor, lcmWindow);
  }
}

export default zoomProofTree;
