import { Editor } from "@tldraw/tldraw";
import { ConvertedProofTree, ProofState } from "types";
import CreateId from "./buildProofTree/services/CreateId";
import getDisplayedId from "../services/getDisplayedId";

// lakesare: I spent very much no time thinking about this, especially after the tldraw update (previously we didn't have metadata in tldraw). If you think there is a cleaner solution - there is.
const highlightProofTree = (
  editor: Editor,
  equivalentIds: ConvertedProofTree["equivalentIds"],
  currentGoal: ProofState["goal"]
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
    getDisplayedId(equivalentIds, currentGoal.mvarId)
  );
  const focusedHypIds = currentGoal.hyps
    .reduce < string[] > ((acc, hyp) => [...acc, ...hyp.fvarIds], [])
      .map((inferiorHypId) => {
        const hypId = getDisplayedId(equivalentIds, inferiorHypId);
        return CreateId.node(hypId);
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

export default highlightProofTree;
