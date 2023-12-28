import React from "react";
import { ConvertedProofTree, DataRow, Highlights, TabledCell } from "types";
import TableCell from "./TableCell";
import HypothesisNode from "./HypothesisNode";

interface TableProps {
  tabledCells: TabledCell[];
  dataRow?: DataRow;
  highlights: Highlights;
  proofTree: ConvertedProofTree;
}
const Table = (props: TableProps) => {
  // Example input: props.tabledCells = [{row: 1}, {row: 2}, {row: 3}, {row: 4}, {row: 5}]
  // Example output: maxRow = 5
  const maxRow = Math.max(...props.tabledCells.map(hyp => hyp.row));
  // Example input: maxRow = 5
  // Example output: rows = [0, 1, 2, 3, 4, 5]
  const rows = Array.from({ length: maxRow + 1 }, (_, i) => i);

  const maxColumn = Math.max(...props.tabledCells.map(hyp => hyp.columnTo));
  const columns = Array.from({ length: maxColumn }, (_, i) => i);

  return (
    <table className="hypothesis-table">
      <tbody>
        {
          props.dataRow &&
          <tr key="dataRow">
            <td colSpan={props.dataRow.width}>
              <div className="data-hypotheses">
                {props.dataRow.hypNodes.map((hypNode, index) =>
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
