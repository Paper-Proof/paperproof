import React from "react";
import { ConvertedProofTree, Highlights, TabledCell, TabledTactic } from "types";
import BoxEl from "src/components/ProofTree/components/BoxEl";
import HypothesisNode from "./HypothesisNode";
import TacticNode from "src/components/TacticNode";

function isBetween(num: number, range: [number, number]): boolean {
  return num >= Math.min(...range) && num <= Math.max(...range);
}

interface TacticProps {
  cell: TabledTactic;
  colSpan: number;
  proofTree: ConvertedProofTree;
}
const Tactic = (props: TacticProps) => {
  const tactic = props.cell.tactic;

  return (
    <>
      {
        tactic.haveBoxIds.length > 0 &&
        <div className="child-boxes">
          {tactic.haveBoxIds.map((haveBoxId) => (
            <BoxEl
              key={haveBoxId}
              box={props.proofTree.boxes.find((box) => box.id === haveBoxId)!}
              proofTree={props.proofTree}
              highlights={null}
            />
          ))}
        </div>
      }
      <TacticNode tactic={props.cell.tactic} shardId={props.cell.shardId}/>
    </>
  );
};

interface TableCellProps {
  rowIndex: number;
  columnIndex: number;
  tabledCells: TabledCell[];
  highlights: Highlights;
  proofTree: ConvertedProofTree;
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
        <HypothesisNode hypNode={cell.hypNode} highlights={props.highlights}/> :
        <Tactic cell={cell} colSpan={colSpan} proofTree={props.proofTree}/>
      }
    </td>;
  } else {
    return null;
  }
};

export default TableCell;
