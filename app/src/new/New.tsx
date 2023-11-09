import React from "react";

import { TransformWrapper, TransformComponent } from "react-zoom-pan-pinch";
import converter from "src/services/updateUI/services/converter";

import { ConvertedProofTree, ProofResponse } from "types";
import { Box } from "./Box";

interface PropsNew {
  proofState: ProofResponse;
}

export const New = (props: PropsNew) => {
  if (!props.proofState || "error" in props.proofState) {
    return
  }

  const proofTree : ConvertedProofTree = converter(props.proofState.proofTree);

  const rootWindow = proofTree.windows.find((w) => w.parentId === null);
  if (!rootWindow) return null

  return <Box/>
}
