import { Editor } from "@tldraw/tldraw";
import { Format, InteractiveGoal } from "../types";
import CreateId from "./buildProofTree/services/CreateId";

// This could be done in /extension, but doing it here for the ease of debugging
const getDisplayedId = (equivalentIds: Format["equivalentIds"], id: string) => {
  const displayedId = Object.keys(equivalentIds).find((displayedId) =>
    equivalentIds[displayedId].find((inferiorId) => inferiorId === id)
  );
  return displayedId ? displayedId : id;
};

// lakesare: I spent very much no time thinking about this, especially after the tldraw update (previously we didn't have metadata in tldraw). If you think there is a cleaner solution - there is.
const focusProofTree = (
  editor: Editor,
  equivalentIds: Format["equivalentIds"],
  currentGoal: InteractiveGoal | null
) => {
  if (currentGoal === null) {
    const existingNodes = editor.currentPageShapes
      .filter((shape) => shape.id.startsWith("shape:node-"))
      .map((node) => ({
        id: node.id,
        type: "customNode",
        meta: {
          isFocused: true
        }
      }));
    editor.updateShapes(existingNodes);
    return;
  }

  const focusedGoalId = CreateId.node(
    editor,
    getDisplayedId(equivalentIds, currentGoal.mvarId)
  );
  const focusedHypIds = currentGoal.hyps
    .reduce < string[] > ((acc, hyp) => [...acc, ...hyp.fvarIds], [])
      .map((inferiorHypId) => {
        const hypId = getDisplayedId(equivalentIds, inferiorHypId);
        return CreateId.node(editor, hypId);
      });
  const focusedShapes = editor.currentPageShapes
    .filter((shape) => shape.id.startsWith("shape:node-"))
    .map((node) => {
      const isFocused =
        node.id === focusedGoalId || focusedHypIds.includes(node.id);
      return {
        id: node.id,
        type: "customNode",
        meta: {
          isFocused: isFocused
        }
      };
    });
  editor.updateShapes(focusedShapes);
};

export default focusProofTree;
