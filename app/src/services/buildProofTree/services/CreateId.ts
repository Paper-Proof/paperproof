import { Editor, TLShapeId, createShapeId } from "@tldraw/tldraw";

// Hmm is app & tacticId & windowId enough
const hypTactic = (editor: Editor, tacticId: string, fromNodeId: string | null, windowId: string | number): TLShapeId => {
  return createShapeId(`hypTactic-${tacticId}-from-${fromNodeId ? fromNodeId : "null"}-window-${windowId}`);
}

const goalTactic = (editor: Editor, tacticId: string): TLShapeId => {
  return createShapeId(`goalTactic-${tacticId}`);
}

const node = (editor: Editor, nodeId: string): TLShapeId => {
  return createShapeId(`node-${nodeId}`);
}

const window = (editor: Editor, windowId: string | number): TLShapeId => {
  return createShapeId(`window-${windowId}`);
}

export default { hypTactic, goalTactic, node, window };
