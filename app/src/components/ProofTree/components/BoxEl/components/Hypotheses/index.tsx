import React from "react";
import { Box } from "types";
import Table from "./components/Table";

interface Props {
  hypTables: Box['hypTables'];
}

const HypothesesComponent = (props: Props) => {
  return props.hypTables.map((hypTable, index) =>
    (hypTable.tabledHyps.length > 0 || hypTable.tabledTactics.length > 0) &&
    <Table key={index} hypTable={hypTable}/>
  )
}

export default HypothesesComponent;
