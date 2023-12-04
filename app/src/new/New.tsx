import React from "react";

import converter from "../library/converter";

import { ConvertedProofTree, ProofResponse } from "types";
import BoxEl from "./BoxEl";

interface PropsNew {
  proofState: ProofResponse;
}

export const New = (props: PropsNew) => {
  if (!props.proofState || "error" in props.proofState) {
    return
  }

  const proofTree : ConvertedProofTree = converter(props.proofState.proofTree);

  const rootBox = proofTree.boxes.find((box) => box.parentId === null);
  if (!rootBox) return null

  return <BoxEl zoomToElement={() => {}} box={rootBox} proofTree={proofTree}/>
}
