import React from "react";
import { TabledCell } from "types";
import HypothesisNode from "./HypothesisNode";
import TacticNodeForHypothesis from "./TacticNodeForHypothesis";

function isBetween(num: number, range: [number, number]): boolean {
  return num >= Math.min(...range) && num <= Math.max(...range);
}

interface TableCellProps {
  rowIndex: number;
  columnIndex: number;
  tabledCells: TabledCell[];
  shouldTacticHaveSelfRespect: boolean;
}
const TableCell = (props: TableCellProps) => {
  const tabledCellsOnThisRow = props.tabledCells.filter((tabledHyp) => tabledHyp.row === props.rowIndex);

  const cell = tabledCellsOnThisRow
    .find((hyp) => isBetween(props.columnIndex, [hyp.columnFrom, hyp.columnTo - 1]));

  if (!cell) {
    return <td/>;
  } else if (cell.columnFrom === props.columnIndex) {
    const colSpan = cell.columnTo - cell.columnFrom;
    return <td colSpan={colSpan}>
      {'hypNode' in cell ?
        <HypothesisNode hypNode={cell.hypNode}/> :
        <TacticNodeForHypothesis cell={cell} colSpan={colSpan} shouldTacticHaveSelfRespect={props.shouldTacticHaveSelfRespect}/>
      }
    </td>;
  } else {
    return null;
  }
};

export default TableCell;
