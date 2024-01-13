import React from "react";
import { ConvertedProofTree, Highlights, Table } from "types";
import TableCell from "./TableCell";
import HypothesisNode from "./HypothesisNode";
import TacticNode from "src/components/TacticNode";

interface TableProps {
  highlights: Highlights;
  proofTree: ConvertedProofTree;
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
    {
      props.hypTable.dataRow &&
      <section className="data">
        <div className="data-hypotheses">
          {props.hypTable.dataRow.hypNodes.map((hypNode, index) =>
            <HypothesisNode key={index} hypNode={hypNode} highlights={props.highlights}/>
          )}
        </div>
        {
          tabledCells.length === 0 &&
          <TacticNode tactic={props.proofTree.tactics.find((tactic) => tactic.text === "init")!} shardId="0"/>
        }
      </section>
    }
    <table className="hypothesis-table">
      <tbody>
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
  </>;
};

export default Table;
