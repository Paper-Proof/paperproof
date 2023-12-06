import React from "react";
import { Highlights, TabledCell } from "types";
import Hint from "../Hint";

function isBetween(num: number, range: [number, number]): boolean {
  return num >= Math.min(...range) && num <= Math.max(...range);
}

interface TableCellProps {
  rowIndex: number;
  columnIndex: number;
  tabledCells: TabledCell[];
  highlights: Highlights;
}

export const TableCell = (props: TableCellProps) => {
  const tabledCellsOnThisRow = props.tabledCells.filter((tabledHyp) => tabledHyp.row === props.rowIndex);

  const cellThatBelongsToThisColumn = tabledCellsOnThisRow
    .find((hyp) => isBetween(props.columnIndex, [hyp.columnFrom, hyp.columnTo - 1]));
  if (!cellThatBelongsToThisColumn) {
    return <td />;
  } else if (cellThatBelongsToThisColumn.columnFrom === props.columnIndex) {
    const colSpan = cellThatBelongsToThisColumn.columnTo - cellThatBelongsToThisColumn.columnFrom;
    return <td colSpan={colSpan}>
      {'hypNode' in cellThatBelongsToThisColumn ?
        <div className={`hypothesis -hint ${!props.highlights || props.highlights.hypIds.includes(cellThatBelongsToThisColumn.hypNode.id) ? "" : "-faded"}`}>
          <Hint>{cellThatBelongsToThisColumn}</Hint>
          <span className="name">{cellThatBelongsToThisColumn.hypNode.name}</span>: {cellThatBelongsToThisColumn.hypNode.text}
        </div> :
        <div className={`tactic -hint ${colSpan > 1 ? "-spans-multiple-hypotheses" : ""}`}>
          <Hint>{cellThatBelongsToThisColumn}</Hint>
          {cellThatBelongsToThisColumn.tactic.text}
        </div>}
    </td>;
  } else {
    return null;
  }
};
