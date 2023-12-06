import React from "react";
import { Highlights, TabledCell } from "types";
import { TableCell } from "./TabledHyp";

interface TableComponentProps {
  tabledCells: TabledCell[];
  highlights: Highlights;
}
const TableComponent = (props: TableComponentProps) => {
  const maxRow = Math.max(...props.tabledCells.map(hyp => hyp.row));
  const rows = Array.from({ length: maxRow + 1 }, (_, i) => i);

  const maxColumn = Math.max(...props.tabledCells.map(hyp => hyp.columnTo));
  const columns = Array.from({ length: maxColumn + 1 }, (_, i) => i);

  return (
    <table>
      <tbody>
        {rows.map((rowIndex) => (
          <tr key={rowIndex}>
            {columns.map((columnIndex) => <TableCell key={columnIndex} columnIndex={columnIndex} rowIndex={rowIndex} tabledCells={props.tabledCells} highlights={props.highlights} />
            )}
          </tr>
        ))}
      </tbody>
    </table>
  );
};

export default TableComponent;
