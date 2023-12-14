import React from "react";
import { ConvertedProofTree, Highlights, TabledCell } from "types";
import TableCell from "./TableCell";

interface TableComponentProps {
  tabledCells: TabledCell[];
  highlights: Highlights;
  proofTree: ConvertedProofTree;
}
const Table = (props: TableComponentProps) => {
  // Example input: props.tabledCells = [{row: 1}, {row: 2}, {row: 3}, {row: 4}, {row: 5}]
  // Example output: maxRow = 5
  const maxRow = Math.max(...props.tabledCells.map(hyp => hyp.row));
  // Example input: maxRow = 5
  // Example output: rows = [0, 1, 2, 3, 4, 5]
  const rows = Array.from({ length: maxRow + 1 }, (_, i) => i);

  const maxColumn = Math.max(...props.tabledCells.map(hyp => hyp.columnTo));
  const columns = Array.from({ length: maxColumn + 1 }, (_, i) => i);

  return (
    <table>
      <tbody>
        {rows.map((rowIndex) => (
          <tr key={rowIndex}>
            {columns.map((columnIndex) =>
              <TableCell
                key={columnIndex}
                proofTree={props.proofTree}
                columnIndex={columnIndex}
                rowIndex={rowIndex}
                tabledCells={props.tabledCells}
                highlights={props.highlights}
              />
            )}
          </tr>
        ))}
      </tbody>
    </table>
  );
};

export default Table;
