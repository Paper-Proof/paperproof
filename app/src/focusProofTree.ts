import { Editor as App, Tldraw } from "@tldraw/tldraw";
import { Format, InteractiveGoal, ProofState } from "./types";
import { createNodeId } from "./buildProofTree/services/CreateId";

// This could be done in /extension, but doing it here for the ease of debugging
const getDisplayedId = (equivalentIds: Format["equivalentIds"], id: string) => {
  const displayedId = Object.keys(equivalentIds).find((displayedId) =>
    equivalentIds[displayedId].find((inferiorId) => inferiorId === id)
  );
  return displayedId ? displayedId : id;
};

const focusProofTree = (
  app: App,
  equivalentIds: Format["equivalentIds"],
  currentGoal: InteractiveGoal | null
) => {
  if (currentGoal === null) {
    const existingNodes = app.shapesArray
      .filter((shape) => shape.id.startsWith("shape:node-"))
      .map((node) => ({
        id: node.id,
        type: "geo",
        // props: {
        //   opacity: "1",
        // },
      }));
    app.updateShapes(existingNodes);
    return;
  }

  const focusedGoalId = createNodeId(
    app,
    getDisplayedId(equivalentIds, currentGoal.mvarId)
  );
  const focusedHypIds = currentGoal.hyps
    .reduce < string[] > ((acc, hyp) => [...acc, ...hyp.fvarIds], [])
      .map((inferiorHypId) => {
        const hypId = getDisplayedId(equivalentIds, inferiorHypId);
        return createNodeId(app, hypId);
      });
  const focusedShapes = app.shapesArray
    .filter((shape) => shape.id.startsWith("shape:node-"))
    .map((node) => {
      const ifFocused =
        node.id === focusedGoalId || focusedHypIds.includes(node.id);
      return {
        id: node.id,
        type: "geo",
        // TODO:update opacity doesn't work
        // props: {
        //   opacity: ifFocused ? "1" : "0.25",
        // },
      };
    });
  app.updateShapes(focusedShapes);
};

export default focusProofTree;
