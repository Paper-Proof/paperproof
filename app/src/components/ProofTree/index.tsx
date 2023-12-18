import React, { useEffect, useState } from "react";
import { ConvertedProofTree, Highlights } from "types";
import BoxEl from "./components/BoxEl";

interface PropsNew {
  proofTree: ConvertedProofTree;
  highlights: Highlights
}

const ProofTree = (props: PropsNew) => {
  const rootBox = props.proofTree.boxes.find((box) => box.parentId === null);
  if (!rootBox) return null;

  return <BoxEl box={rootBox} proofTree={props.proofTree} highlights={props.highlights}/>;
}

export default ProofTree;
