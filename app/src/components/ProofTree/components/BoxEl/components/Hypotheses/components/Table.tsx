import React from "react";
import { ConvertedProofTree, DataRow, Highlights, TabledCell, Table } from "types";
import TableCell from "./TableCell";
import HypothesisNode from "./HypothesisNode";

interface TableProps {
  highlights: Highlights;
  proofTree: ConvertedProofTree;
  hypTable: Table;
}
const Table = (props: TableProps) => {
  const dataRow = props.hypTable.dataRow;
  const tabledCells = [...props.hypTable.tabledHyps, ...props.hypTable.tabledTactics];

  // Example input: tabledCells = [{row: 1}, {row: 2}, {row: 3}, {row: 4}, {row: 5}]
  // Example output: maxRow = 5
  const maxRow = Math.max(...tabledCells.map(hyp => hyp.row));
  // Example input: maxRow = 5
  // Example output: rows = [0, 1, 2, 3, 4, 5]
  const rows = Array.from({ length: maxRow + 1 }, (_, i) => i);
  
  const maxColumn = Math.max(...tabledCells.map(hyp => hyp.columnTo));
  const columns = Array.from({ length: maxColumn }, (_, i) => i);

  return (
    <table className="hypothesis-table">
      <tbody>
        {
          dataRow &&
          <tr key="dataRow">
            <td colSpan={dataRow.width}>
              <div className="data-hypotheses">
                {dataRow.hypNodes.map((hypNode, index) =>
                  <HypothesisNode key={index} hypNode={hypNode} highlights={props.highlights}/>
                )}
              </div>
            </td>
          </tr>
        }
        {rows.map((rowIndex) => (
          <tr key={rowIndex}>
            {columns.map((columnIndex) =>
              <TableCell
                key={columnIndex}
                proofTree={props.proofTree}
                columnIndex={columnIndex}
                rowIndex={rowIndex}
                tabledCells={tabledCells}
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
