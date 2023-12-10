import React, { useEffect, useState } from "react";
import { ConvertedProofTree, Highlights, ProofResponse } from "types";
import BoxEl from "./components/BoxEl";

interface PropsNew {
  proofTree: ConvertedProofTree;
  highlights: Highlights
}

const ProofTree = (props: PropsNew) => {
  // const [leaderLines, setLeaderLines] = useState<LeaderLine[]>([]);

  // useEffect(() => {
  //   // Remove previous leaderLines if they exist
  //   leaderLines.forEach((leaderLine) => {
  //     leaderLine.remove();
  //   });
  //   // Create new leaderLines and store them in state
  //   const newLeaderLines = createDependsOnArrows(props.proofTree)
  //   setLeaderLines(newLeaderLines);
  // }, [props.proofTree]);

  const rootBox = props.proofTree.boxes.find((box) => box.parentId === null);
  if (!rootBox) return null;

  return <BoxEl box={rootBox} proofTree={props.proofTree} highlights={props.highlights}/>
}

export default ProofTree