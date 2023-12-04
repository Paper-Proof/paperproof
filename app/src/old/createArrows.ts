import { Editor, TLShapeId } from "@tldraw/tldraw";
import { UIShared, UIElement, ConvertedProofTree } from "types";
import DrawShape from './updateUI/services/buildProofTree/services/DrawShape';
import CreateId from './updateUI/services/buildProofTree/services/CreateId';

const findIdInApp = (editor: Editor, desiredId: TLShapeId): TLShapeId | null => {
  const existingShapeIds = editor.currentPageShapes;
  const desiredShape = editor.getShape(desiredId);

  if (desiredShape) {
    return desiredShape.id;
  } else {
    console.log(`Didn't find ${desiredId} in:`);
    console.log(existingShapeIds);
    return null
  }
}

const getWindowByHypId = (proofTree: ConvertedProofTree, hypId : string) =>
  proofTree.boxes.find((window) =>
    window.hypNodes.find((hypLayer) => hypLayer.find((hyp) => hyp.id === hypId))
  );

const findWindowId = (editor: Editor, proofTree: ConvertedProofTree, goalId: string): TLShapeId | null => {
  const window = proofTree.boxes.find((window) =>
    window.goalNodes.find((goalNode) => goalNode.id === goalId)
  );
  if (window) {
    return findIdInApp(editor, CreateId.window(window.id));
  } else {
    return null;
  }
}

const createArrows = (shared: UIShared): UIElement => {
  return {
    size: [0, 0],
    draw: (x: number, y: number) => {
      shared.proofTree.tactics.forEach((tactic) => {
        // 1. Draw arrows between this tactic and hypotheses
        tactic.hypArrows.forEach((hypArrow) => {
          hypArrow.toIds.forEach((toId) => {
            const window = getWindowByHypId(shared.proofTree, toId);
            if (!window) return

            if (hypArrow.fromId) {
              const fromNodeId = findIdInApp(shared.editor, CreateId.node(hypArrow.fromId));
              const toTacticId = findIdInApp(shared.editor, CreateId.hypTactic(tactic.id, hypArrow.fromId, window.id));
              if (!fromNodeId || !toTacticId) return
              DrawShape.arrow(shared.editor, fromNodeId, toTacticId, "hypArrow");
            }
            const fromTacticId = findIdInApp(shared.editor, CreateId.hypTactic(tactic.id, hypArrow.fromId, window.id));
            const toNodeId = findIdInApp(shared.editor, CreateId.node(toId));
            if (!fromTacticId || !toNodeId) return
            DrawShape.arrow(shared.editor, fromTacticId, toNodeId, "hypArrow");
          });
        });

        // 2. Draw arrows between this tactic and goals
        tactic.goalArrows.forEach((goalArrow) => {
          const tacticId = findIdInApp(shared.editor, CreateId.goalTactic(tactic.id));
          const toNodeId = findIdInApp(shared.editor, CreateId.node(goalArrow.fromId));
          const fromNodeId = findIdInApp(shared.editor, CreateId.node(goalArrow.toId));

          const windowId1 = findWindowId(shared.editor, shared.proofTree, goalArrow.fromId);
          const windowId2 = findWindowId(shared.editor, shared.proofTree, goalArrow.toId);
          if (!tacticId || !toNodeId || !fromNodeId || !windowId1 || !windowId2) return
          if (windowId1 === windowId2) {
            DrawShape.arrow(shared.editor, fromNodeId, tacticId, "goalArrow");
          } else {
            DrawShape.arrow(shared.editor, windowId2, tacticId, "goalArrow");
          }

          DrawShape.arrow(shared.editor, tacticId, toNodeId, "goalArrow");
        });

        // 3. Draw arrows between this tactic and `have` windows
        for (const haveWindowId of tactic.haveBoxIds) {
          if (tactic.hypArrows[0]) {
            const window = getWindowByHypId(
              shared.proofTree,
              tactic.hypArrows[0].toIds[0]
            );
            if (!window) return;
            const fromWindowId = findIdInApp(
              shared.editor,
              CreateId.window(haveWindowId)
            );
            const toTacticId = findIdInApp(
              shared.editor,
              CreateId.hypTactic(tactic.id, null, window.id)
            );
            if (!fromWindowId || !toTacticId) return;
            DrawShape.arrow(
              shared.editor,
              fromWindowId,
              toTacticId,
              "goalArrow"
            );
          }
        }
      });
    }
  };
}

export default createArrows;
