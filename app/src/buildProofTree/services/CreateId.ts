import { App, TLShapeId } from "@tldraw/tldraw";

const createHypTacticId = (app: App, tacticId: string, fromNodeId: string | null): TLShapeId => {
  return app.createShapeId(`hypTactic-${tacticId}-from-${fromNodeId ? fromNodeId : "null"}`);
}

const createGoalTacticId = (app: App, tacticId: string): TLShapeId => {
  return app.createShapeId(`goalTactic-${tacticId}`);
}

const createNodeId = (app: App, nodeId: string): TLShapeId => {
  return app.createShapeId(`node-${nodeId}`);
}

const createWindowId = (app: App, windowId: string | number): TLShapeId => {
  return app.createShapeId(`window-${windowId}`);
}

export { createHypTacticId, createGoalTacticId, createNodeId, createWindowId };
