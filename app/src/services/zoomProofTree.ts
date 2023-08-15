import { Editor } from '@tldraw/tldraw';
import CreateId from './buildProofTree/services/CreateId';
import zoomToWindow from './zoomToWindow';

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

export default zoomProofTree;
