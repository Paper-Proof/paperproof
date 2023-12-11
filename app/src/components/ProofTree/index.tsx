import React, { useEffect, useState } from "react";
import { ConvertedProofTree, Highlights, ProofResponse } from "types";
import BoxEl from "./components/BoxEl";
import converter from "src/services/converter";
import getHighlights from "./services/getHighlights";
// @ts-ignore
import LeaderLine from './services/LeaderLine.min.js';
import createDependsOnArrows from '../../services/createDependsOnArrows';

interface PropsNew {
  proofTree: ConvertedProofTree;
  highlights: Highlights
}

const ProofTree = (props: PropsNew) => {
  const [leaderLines, setLeaderLines] = useState<LeaderLine[]>([]);

  useEffect(() => {
    leaderLines.forEach((leaderLine) => {
      leaderLine.remove();
    });
    const newLeaderLines = createDependsOnArrows(props.proofTree)
    setLeaderLines(newLeaderLines);
  }, [props.proofTree]);

  const rootBox = props.proofTree.boxes.find((box) => box.parentId === null);
  if (!rootBox) return null;

  return <BoxEl box={rootBox} proofTree={props.proofTree} highlights={props.highlights}/>;
}

export default ProofTree;
