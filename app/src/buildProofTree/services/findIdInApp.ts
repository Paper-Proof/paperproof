import { App, TLShapeId } from "@tldraw/tldraw";

const findIdInApp = (app: App, desiredId: TLShapeId): TLShapeId | null => {
  const existingShapeIds = Array.from(app.shapeIds.values());
  const foundId = existingShapeIds.find((shapeId) => shapeId === desiredId)
  if (foundId) {
    return foundId;
  }

  console.log(`Didn't find ${desiredId} in:`);
  console.log(existingShapeIds);

  return null
}

export default findIdInApp;
