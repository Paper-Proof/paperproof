import { Editor as App, TLShapeId, createShapeId } from "@tldraw/tldraw";

// Hmm is app & tacticId & windowId enough
const hypTactic = (app: App, tacticId: string, fromNodeId: string | null, windowId: string | number): TLShapeId => {
  return createShapeId(`hypTactic-${tacticId}-from-${fromNodeId ? fromNodeId : "null"}-window-${windowId}`);
}

const goalTactic = (app: App, tacticId: string): TLShapeId => {
  return createShapeId(`goalTactic-${tacticId}`);
}

const node = (app: App, nodeId: string): TLShapeId => {
  return createShapeId(`node-${nodeId}`);
}

const window = (app: App, windowId: string | number): TLShapeId => {
  return createShapeId(`window-${windowId}`);
}

export default { hypTactic, goalTactic, node, window };
