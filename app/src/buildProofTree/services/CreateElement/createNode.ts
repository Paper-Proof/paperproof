import { TLParentId } from "@tldraw/tldraw";
import { IdElement, Shared } from "../../../types";

import getTextSize from '../getTextSize';

import { drawShapeTactic, drawShapeGoal, drawShapeHypothesis, drawShapeGoalUsername } from '../DrawShape';

const createNode = (
  shared: Shared,
  parentId: TLParentId | undefined,
  text: string,
  type: "hypothesis" | "tactic" | "goal" | "goalUsername",
  // This is for arrows
  externalId: string,
  ids: string[] = [],
): IdElement => {
  const newText = text + (localStorage.getItem("dev") === 'true' ? '      ' + externalId : '');
  const id = shared.app.createShapeId(externalId);
  const [w, h] = getTextSize(shared.app, newText);
  return {
    id,
    size: [w, h],
    draw(x, y, prefferedWidth?: number) {
      const isCurrentGoal = ids.includes(shared.currentGoal);
      const effectiveW = !!prefferedWidth && prefferedWidth > w ? prefferedWidth : w;
      if (type === "tactic") {
        drawShapeTactic(shared.app, id, parentId, x, y, effectiveW, h, newText);
      } else if (type === "goal") {
        drawShapeGoal(shared.app, id, parentId, x, y, effectiveW, h, newText, isCurrentGoal);
      } else if (type === "hypothesis") {
        drawShapeHypothesis(shared.app, id, parentId, x, y, effectiveW, h, newText);
      } else if (type === "goalUsername") {
        drawShapeGoalUsername(shared.app, id, parentId, x, y, effectiveW, h, newText);
      }
    }
  }
};

export default createNode;
