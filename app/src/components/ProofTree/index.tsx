import React from "react";
import { ConvertedProofTree, ProofResponse } from "types";
import BoxEl from "./components/BoxEl";
import converter from "src/services/converter";
import getHighlights from "./services/getHighlights";

interface PropsNew {
  proofState: ProofResponse;
}

const ProofTree = (props: PropsNew) => {
  if (!props.proofState || "error" in props.proofState) {
    return;
  }

  const proofTree : ConvertedProofTree = converter(props.proofState.proofTree);
  const highlights = getHighlights(proofTree.equivalentIds, props.proofState.goal);

  const rootBox = proofTree.boxes.find((box) => box.parentId === null);
  if (!rootBox) return null;

  return <BoxEl box={rootBox} proofTree={proofTree} highlights={highlights}/>
}

export default ProofTree