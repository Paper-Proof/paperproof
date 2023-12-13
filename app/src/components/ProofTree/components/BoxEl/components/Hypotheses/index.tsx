import React from "react";
import { ConvertedProofTree, HypNode, Highlights } from "types";
import Table from "./components/Table";
import hypLayersToTabledCells from "./services/hypLayersToTabledHyps";

interface Props {
  proofTree: ConvertedProofTree;
  highlights: Highlights;
  hypLayers: HypNode[][];
}

const HypothesesComponent = (props: Props) => {
  const tabledCells = hypLayersToTabledCells(props.hypLayers, props.proofTree);
  return <Table proofTree={props.proofTree} highlights={props.highlights} tabledCells={tabledCells}/>
}

export default HypothesesComponent;
