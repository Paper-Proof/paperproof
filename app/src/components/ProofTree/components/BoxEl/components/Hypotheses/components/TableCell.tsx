import React from "react";
import { ConvertedProofTree, Highlights, TabledCell, TabledHyp, TabledTactic } from "types";
import Hint from "../../Hint";
import BoxEl from "src/components/ProofTree/components/BoxEl";

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

const ourHypothesisTactic = {
  "id": "4", "text": "cases' hm with p q",
  "dependsOnIds": ["_uniq.10026"],
  "goalArrows": [{"fromId": "_uniq.10027", "toId": "_uniq.10073"}, {"fromId": "_uniq.10027", "toId": "_uniq.10087"}],
  "hypArrows": [{"fromId": "_uniq.10026", "toIds": ["_uniq.10059"]}, {"fromId": "_uniq.10026", "toIds": ["_uniq.10074"]}],
  "haveBoxIds": []
}
// We shall look into the hypothesis tactic we found (`ourHypothesisTactic`), and look at its `ourHypothesisTactic.hypArrows`. Then we're searching for our personal parent!
// 1. Do we have a parent that's in another window? Draw an arrow.
// 2. Do we have a parent that's multiple rows above us? Draw an arrow.

interface TacticProps {
  cell: TabledTactic;
  colSpan: number;
  proofTree: ConvertedProofTree;
}
const Tactic = (props: TacticProps) => {
  const tactic = props.cell.tactic;

  const doesSpan = tactic.haveBoxIds.length > 0 || props.colSpan > 1;

  return (
    <>
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
      <div className={`tactic -hint ${doesSpan ? "-spans-multiple-hypotheses" : ""}`}>
        <Hint>{props.cell}</Hint>
        {tactic.text}
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
