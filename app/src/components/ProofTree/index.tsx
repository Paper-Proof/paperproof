import React from "react";
import BoxEl from "./components/BoxEl";
import { useGlobalContext } from "src/indexBrowser";

const ProofTree = () => {
  const { proofTree } = useGlobalContext();
  const rootBox = proofTree.boxes.find((box) => box.parentId === null);
  if (!rootBox) return null;

  return <BoxEl box={rootBox}/>;
}

export default ProofTree;
