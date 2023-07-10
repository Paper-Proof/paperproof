import { TLParentId } from "@tldraw/tldraw";
import { Element, Window, Shared } from "../../../types";
import withPadding from '../withPadding';
import { drawShapeWindow } from '../DrawShape';
import createWindowInsides from './createWindowInsides';
import { createWindowId } from '../CreateId';

const goalUsernameHeight = 38;

const createWindow = (shared: Shared, parentId: TLParentId | undefined, window: Window, depth: number): Element => {
  const goalUsername = window.goalNodes[0].name;
  const ifShowGoalUsername = !(localStorage.getItem("hideGoalUsernames") || goalUsername === "[anonymous]");

  const frameId = createWindowId(shared.app, window.id);
  const nodes = withPadding(
    {
      left: shared.framePadding,
      right: shared.framePadding,
      top: shared.framePadding,
      bottom: ifShowGoalUsername ? goalUsernameHeight : 0
    },
    createWindowInsides(shared, frameId, window, depth)
  );

  const [w, h] = nodes.size;

  return {
    size: [w, h],
    draw: (x: number, y: number) => {
      drawShapeWindow(shared.app, frameId, parentId, x, y, w, h, depth, ifShowGoalUsername ? goalUsername : null, goalUsernameHeight);
      nodes.draw(0, 0);
    }
  };
}

export default createWindow;
