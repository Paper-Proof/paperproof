import React from "react";
import { ConvertedProofTree, HypNode, Highlights, Box } from "types";
import Table from "./components/Table";
import hypLayersToTabledCells from "./services/hypLayersToTabledHyps";

interface Props {
  proofTree: ConvertedProofTree;
  highlights: Highlights;
  hypLayers: Box['hypLayers'];
}

const HypothesesComponent = (props: Props) => {
  const tables = hypLayersToTabledCells(props.hypLayers, props.proofTree);

  return tables.map((table, index) =>
    <Table key={index} proofTree={props.proofTree} dataRow={table.dataRow} highlights={props.highlights} tabledCells={[...table.tabledHyps, ...table.tabledTactics]}/>
  )
}

export default HypothesesComponent;
