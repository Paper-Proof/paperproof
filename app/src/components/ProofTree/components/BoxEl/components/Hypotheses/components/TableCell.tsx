import React from "react";
import { TabledCell, TabledTactic } from "types";
import BoxEl from "src/components/ProofTree/components/BoxEl";
import HypothesisNode from "./HypothesisNode";
import TacticNode from "src/components/TacticNode";
import { useGlobalContext } from "src/indexBrowser";

function isBetween(num: number, range: [number, number]): boolean {
  return num >= Math.min(...range) && num <= Math.max(...range);
}

interface TacticProps {
  cell: TabledTactic;
  colSpan: number;
}
const Tactic = (props: TacticProps) => {
  const { proofTree } = useGlobalContext();
  const tactic = props.cell.tactic;

  if (tactic.text === "init") return null

  return (
    <>
      {
        tactic.haveBoxIds.length > 0 &&
        <div className="child-boxes">
          {tactic.haveBoxIds.map((haveBoxId) => (
            <BoxEl
              key={haveBoxId}
              box={proofTree.boxes.find((box) => box.id === haveBoxId)!}
              // highlights={null}
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
  shouldTacticsHaveSelfRespect: boolean;
}
const TableCell = (props: TableCellProps) => {
  const tabledCellsOnThisRow = props.tabledCells.filter((tabledHyp) => tabledHyp.row === props.rowIndex);

  const cell = tabledCellsOnThisRow
    .find((hyp) => isBetween(props.columnIndex, [hyp.columnFrom, hyp.columnTo - 1]));

  if (!cell) {
    return <td/>;
  } else if (cell.columnFrom === props.columnIndex) {
    const colSpan = cell.columnTo - cell.columnFrom;
    return <td colSpan={colSpan} className={props.shouldTacticsHaveSelfRespect ? "-add-self-respect-to-tactics" : ""}>
      {'hypNode' in cell ?
        <HypothesisNode hypNode={cell.hypNode}/> :
        <Tactic cell={cell} colSpan={colSpan}/>
      }
    </td>;
  } else {
    return null;
  }
};

export default TableCell;
