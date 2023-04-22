import Vec from "@tldraw/vec";
import { Action } from "state/constants";
import { mutables } from "state/mutables";

export const translateSelectedShapes: Action = (data) => {
  const { initialPoint, currentPoint, snapshot } = mutables;

  let delta = Vec.sub(currentPoint, initialPoint);

  data.pageState.selectedIds.forEach((id) => {
    const initialShape = snapshot.page.shapes[id];
    const movedShape = data.page.shapes[id];
    movedShape.point = Vec.add(initialShape.point, delta);
  });
};
