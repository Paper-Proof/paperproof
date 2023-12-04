import { Editor, TLShapeId, createShapeId } from "@tldraw/tldraw";
import { UIShared, UIElement, ConvertedProofTree } from "types";
import DrawShape from '../DrawShape';
import CreateId from '../CreateId';

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

const createDependsOnArrows = (shared: UIShared): UIElement => {
  return {
    size: [0, 0],
    draw: (x: number, y: number) => {
      shared.proofTree.tactics.forEach((tactic) => {
        if (!tactic.successGoalId) return;
        tactic.dependsOnIds.forEach((dependsOnHypId) => {
          const fromNodeId = findIdInApp(shared.editor, CreateId.node(dependsOnHypId));

          const toTactic = shared.editor.currentPageShapes.find((shape) => {
            return shape.id === CreateId.goalTactic(tactic.id)
         })

          if (!fromNodeId || !toTactic) return
          DrawShape.arrow(shared.editor, fromNodeId, toTactic.id, "successArrow");
        });
      });
    }
  };
}

export default createDependsOnArrows;
