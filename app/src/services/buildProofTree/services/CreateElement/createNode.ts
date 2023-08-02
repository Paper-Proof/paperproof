import { TLParentId, TLShapeId } from "@tldraw/tldraw";
import { IdElement, Shared } from "../../../../types";

import getTextSize from '../getTextSize';

import DrawShape from '../DrawShape';

const createNode = (
  shared: Shared,
  parentId: TLParentId | undefined,
  text: string,
  type: "hypothesis" | "tactic" | "goal",
  // This is for arrows
  id: TLShapeId
): IdElement => {
  const newText = text + (localStorage.getItem("dev") === 'true' ? '      ' + id : '');
  const [w, h] = getTextSize(shared.app, newText);
  return {
    id,
    size: [w, h],
    draw(x, y, prefferedWidth?: number) {
      const effectiveW = !!prefferedWidth && prefferedWidth > w ? prefferedWidth : w;
      if (type === "tactic") {
        DrawShape.tactic(shared.app, id, parentId, x, y, effectiveW, h, newText);
      } else if (type === "goal") {
        DrawShape.goal(shared.app, id, parentId, x, y, effectiveW, h, newText);
      } else if (type === "hypothesis") {
        DrawShape.hypothesis(shared.app, id, parentId, x, y, effectiveW, h, newText);
      }
    }
  }
};

export default createNode;
