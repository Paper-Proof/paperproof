import React from "react";
import { ConvertedProofTree, HypNode, Highlights, Box } from "types";
import Table from "./components/Table";
import hypLayersToTabledCells from "./services/hypLayersToTabledHyps";
// @ts-ignore
import LeaderLine from 'src/services/LeaderLine.min.js';

interface Props {
  proofTree: ConvertedProofTree;
  highlights: Highlights;
  hypLayers: Box['hypLayers'];
}

const options = {
  path: "straight",
  startSocket: "bottom",
  endSocket: "top",
  size: 3,
  // hide: true
}

const HypothesesComponent = (props: Props) => {
  const tables = hypLayersToTabledCells(props.hypLayers, props.proofTree);

  React.useEffect(() => {
    tables.forEach((table) => {
      table.tabledTactics.forEach((tabledTactic) => {
        if (!tabledTactic.arrowFrom) return
        const hypEl = document.getElementById(`hypothesis-${tabledTactic.arrowFrom}`);
        const tacticEl = document.getElementById(`tactic-${tabledTactic.tactic.id}-${tabledTactic.shardId}`);
        console.log({ hypEl, tacticEl });
        if (!hypEl || !tacticEl) return;
        new LeaderLine(hypEl, tacticEl, options);
      })
    })
  }, []);

  return tables.map((table, index) =>
    <Table key={index} proofTree={props.proofTree} dataRow={table.dataRow} highlights={props.highlights} tabledCells={[...table.tabledHyps, ...table.tabledTactics]}/>
  )
}

export default HypothesesComponent;
