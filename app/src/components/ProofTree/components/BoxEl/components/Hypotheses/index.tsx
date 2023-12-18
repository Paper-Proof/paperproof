import React from "react";
import { ConvertedProofTree, HypNode, Highlights, Box } from "types";
import Table from "./components/Table";

interface Props {
  proofTree: ConvertedProofTree;
  highlights: Highlights;
  hypTables: Box['hypTables'];
}

const HypothesesComponent = (props: Props) => {
  return props.hypTables.map((table, index) =>
    <Table key={index} proofTree={props.proofTree} dataRow={table.dataRow} highlights={props.highlights} tabledCells={[...table.tabledHyps, ...table.tabledTactics]}/>
  )
}

export default HypothesesComponent;
