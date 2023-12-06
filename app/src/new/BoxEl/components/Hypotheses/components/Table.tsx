import React from "react";
import { ConvertedProofTree, Highlights, TabledCell } from "types";
import TableCell from "./TableCell";

interface TableComponentProps {
  tabledCells: TabledCell[];
  highlights: Highlights;
  proofTree: ConvertedProofTree;
}
const Table = (props: TableComponentProps) => {
  const maxRow = Math.max(...props.tabledCells.map(hyp => hyp.row));
  const rows = Array.from({ length: maxRow + 1 }, (_, i) => i);

  const maxColumn = Math.max(...props.tabledCells.map(hyp => hyp.columnTo));
  const columns = Array.from({ length: maxColumn + 1 }, (_, i) => i);

  return (
    <table>
      <tbody>
        {rows.map((rowIndex) => (
          <tr key={rowIndex}>
            {columns.map((columnIndex) => <TableCell proofTree={props.proofTree} key={columnIndex} columnIndex={columnIndex} rowIndex={rowIndex} tabledCells={props.tabledCells} highlights={props.highlights} />
            )}
          </tr>
        ))}
      </tbody>
    </table>
  );
};

export default Table;
