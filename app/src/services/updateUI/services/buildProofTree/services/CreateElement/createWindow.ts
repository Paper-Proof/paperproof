import { TLParentId } from "@tldraw/tldraw";
import { UIElement, Window, UIShared } from "types";
import withPadding from '../withPadding';
import DrawShape from '../DrawShape';
import createWindowInsides from './createWindowInsides';
import CreateId from '../CreateId';

const goalUsernameHeight = 38;

// "a._@.Mathlib.Init.Algebra.Order._hyg.1764" => "a"
// (https://github.com/leanprover/lean4/blob/d37bbf4292c72798afdff8bf5488df09193fde58/src/Init/Prelude.lean#L4132)
// Note: I was doing this in the parser with `.eraseMacroScopes`, but we depend in hygienic goal usernames, might be dangerous - so I moved it here.
const prettifyGoalUsername = (username : string) => {
  return username.split('._@')[0];
}

const createWindow = (shared: UIShared, parentId: TLParentId | undefined, window: Window, depth: number): UIElement => {
  const goalUsername = prettifyGoalUsername(window.goalNodes[0].name);
  const ifShowGoalUsername = !(localStorage.getItem("hideGoalUsernames") || goalUsername === "[anonymous]");

  const frameId = CreateId.window(window.id);
  const nodes = withPadding(
    {
      left: shared.framePadding,
      right: shared.framePadding,
      top: shared.framePadding,
      bottom: ifShowGoalUsername ? goalUsernameHeight : (parentId ? 0 : 3)
    },
    createWindowInsides(shared, frameId, window, depth)
  );

  const [w, h] = nodes.size;

  return {
    size: [w, h],
    draw: (x: number, y: number) => {
      DrawShape.window(shared.editor, frameId, parentId, x, y, w, h, depth, ifShowGoalUsername ? goalUsername : null, goalUsernameHeight, window.id);
      nodes.draw(0, 0);
    }
  };
}

export default createWindow;
