import { TLShapeId, createShapeId } from "@tldraw/tldraw";

// Hmm is app & tacticId & windowId enough
const hypTactic = (tacticId: string, fromNodeId: string | null, windowId: string | number): TLShapeId => {
  return createShapeId(`hypTactic-${tacticId}-from-${fromNodeId ? fromNodeId : "null"}-window-${windowId}`);
}

const goalTactic = (tacticId: string): TLShapeId => {
  return createShapeId(`goalTactic-${tacticId}`);
}

const node = (nodeId: string): TLShapeId => {
  return createShapeId(`node-${nodeId}`);
}

const window = (windowId: string | number): TLShapeId => {
  return createShapeId(`window-${windowId}`);
}

export default { hypTactic, goalTactic, node, window };
