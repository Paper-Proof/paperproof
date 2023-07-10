import { App, TLShapeId } from "@tldraw/tldraw";

const findIdInApp = (app: App, id: string): TLShapeId | null => {
  const desiredId = app.createShapeId(id);
  const existingShapeIds = Array.from(app.shapeIds.values());
  const foundId = existingShapeIds.find((shapeId) => shapeId === desiredId)
  if (foundId) {
    return foundId;
  }

  return null
}

export default findIdInApp;
