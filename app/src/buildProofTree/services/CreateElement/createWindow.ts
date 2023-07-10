import { TLParentId } from "@tldraw/tldraw";

import { Element, Window, Shared } from "../../../types";

import vStack from '../vStack';
import withPadding from '../withPadding';
import withWidth from '../withWidth';

import { drawShapeWindow } from '../DrawShape';

import createWindowInsides from './createWindowInsides';
import createNode from './createNode';

const createWindow = (shared: Shared, parentId: TLParentId | undefined, window: Window, depth: number): Element => {
  const frameId = shared.app.createShapeId(`window-${window.id}`);
  const nodes = withPadding(
    { left: shared.framePadding, right: shared.framePadding, top: shared.framePadding, bottom: 0 },
    createWindowInsides(shared, frameId, window, depth)
  );

  let layout: Element;
  const goalUsername = window.goalNodes[0].name;
  if (localStorage.getItem("hideGoalUsernames") || goalUsername === "[anonymous]") {
    layout = vStack(0, [nodes]);
  } else {
    const title = createNode(shared, frameId, goalUsername, "goalUsername", `window-name-node-${window.id}`);
    layout = vStack(0, [nodes, withWidth(nodes.size[0], title)]);
  }

  const [w, h] = layout.size;

  return {
    size: [w, h],
    draw: (x: number, y: number) => {
      drawShapeWindow(shared.app, frameId, parentId, x, y, w, h, depth);
      layout.draw(0, 0);
    }
  };
}

export default createWindow;
