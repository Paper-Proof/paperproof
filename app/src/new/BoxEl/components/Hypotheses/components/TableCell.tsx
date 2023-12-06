import React from "react";
import { ConvertedProofTree, Highlights, TabledCell, TabledHyp, TabledTactic } from "types";
import Hint from "../../Hint";
import BoxEl from "src/new/BoxEl";

function isBetween(num: number, range: [number, number]): boolean {
  return num >= Math.min(...range) && num <= Math.max(...range);
}

interface HypothesisProps {
  cell: TabledHyp;
  highlights: Highlights;
}

const Hypothesis = (props: HypothesisProps) => {
  return <div className={`hypothesis -hint ${!props.highlights || props.highlights.hypIds.includes(props.cell.hypNode.id) ? "" : "-faded"}`}>
    <Hint>{props.cell}</Hint>
    <span className="name">{props.cell.hypNode.name}</span>: {props.cell.hypNode.text}
  </div>
}

interface TacticProps {
  cell: TabledTactic;
  colSpan: number;
  proofTree: ConvertedProofTree;
}

const Tactic = (props: TacticProps) => {
  const doesSpan = props.cell.tactic.haveBoxIds.length > 0 || props.colSpan > 1;
  return (
    <>
      <div className="child-boxes">
        {props.cell.tactic.haveBoxIds.map((haveBoxId) => (
          <BoxEl
            key={haveBoxId}
            box={props.proofTree.boxes.find((box) => box.id === haveBoxId)!}
            proofTree={props.proofTree}
            highlights={null}
          />
        ))}
      </div>
      <div className={`tactic -hint ${doesSpan ? "-spans-multiple-hypotheses" : ""}`}>
        <Hint>{props.cell}</Hint>
        {props.cell.tactic.text}
      </div>
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
        <Hypothesis cell={cell} highlights={props.highlights}/> :
        <Tactic cell={cell} colSpan={colSpan} proofTree={props.proofTree}/>
      }
    </td>;
  } else {
    return null;
  }
};

export default TableCell;
