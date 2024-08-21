import React from "react";
import { Table } from "types";
import TableCell from "./TableCell";

interface TableProps {
  hypTable: Table;
}
const Table = (props: TableProps) => {
  const tabledCells = [...props.hypTable.tabledHyps, ...props.hypTable.tabledTactics];

  // Example input: tabledCells = [{row: 1}, {row: 2}, {row: 3}, {row: 4}, {row: 5}]
  // Example output: maxRow = 5
  const maxRow = Math.max(...tabledCells.map(hyp => hyp.row));
  // Example input: maxRow = 5
  // Example output: rows = [0, 1, 2, 3, 4, 5]
  const rows = Array.from({ length: maxRow + 1 }, (_, i) => i);
  
  const maxColumn = Math.max(...tabledCells.map(hyp => hyp.columnTo));
  const columns = Array.from({ length: maxColumn }, (_, i) => i);

  return <>
    <table className="hypothesis-table">
      <tbody>
        {rows.map((rowIndex) => (
          <tr key={rowIndex}>
            {columns.map((columnIndex) =>
              <TableCell
                key={columnIndex}
                columnIndex={columnIndex}
                shouldTacticHaveSelfRespect={columns.length === 1 && rows.length === 2}
                rowIndex={rowIndex}
                tabledCells={tabledCells}
              />
            )}
          </tr>
        ))}
      </tbody>
    </table>
  </>;
};

export default Table;
