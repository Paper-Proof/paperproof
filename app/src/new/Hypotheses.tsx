import React from "react";

import { ConvertedProofTree, Box, HypNode, Tactic, Highlights } from "types";
import BoxEl from "./BoxEl";
import Hint from "./Hint";

interface Props {
  proofTree: ConvertedProofTree;
  hypLayers: HypNode[][];
  highlights: Highlights;
}

const whichTacticBirthedThisHypothesis = (proofTree: ConvertedProofTree, hypNode: HypNode) : Tactic => {
  const tactic = proofTree.tactics.find((tactic) => tactic.hypArrows.find((hypArrow) => hypArrow.toIds.includes(hypNode.id)));
  return tactic || { text: "init" };
}

const getHypAbove = (proofTree : ConvertedProofTree, tabledHyps : TabledHyp[], hypNode: HypNode) : TabledHyp | undefined => {
  let tabledHypInThisBox : TabledHyp | undefined = undefined;
  proofTree.tactics.find((tactic) => {
    const hypArrow = tactic.hypArrows.find((hypArrow) =>
      hypArrow.toIds.includes(hypNode.id)
    );

    if (hypArrow) {
      tabledHypInThisBox = tabledHyps.find((tabledHyp) =>
        tabledHyp.hypNode.id == hypArrow.fromId
      );
      return true;
    }
  });
  return tabledHypInThisBox;
}

interface TabledHyp {
  hypNode : HypNode;
  columnFrom : number;
  columnTo : number;
  row : number;
}

interface TabledTactic {
  tactic : Tactic;
  columnFrom : number;
  columnTo : number;
  row : number;
}

type TabledCell = TabledHyp | TabledTactic;

function isBetween(num: number, range: [number, number]): boolean {
  return num >= Math.min(...range) && num <= Math.max(...range);
}

interface TableCellProps {
  rowIndex: number;
  columnIndex: number;
  tabledCells: TabledCell[];
  highlights: Highlights;
}

const TableCell = (props: TableCellProps) => {
  const tabledCellsOnThisRow = props.tabledCells.filter((tabledHyp) => tabledHyp.row === props.rowIndex);

  const cellThatBelongsToThisColumn = tabledCellsOnThisRow
    .find((hyp) => isBetween(props.columnIndex, [hyp.columnFrom, hyp.columnTo - 1]));
  if (!cellThatBelongsToThisColumn) {
    return <td/>
  } else if (cellThatBelongsToThisColumn.columnFrom === props.columnIndex) {
    const colSpan = cellThatBelongsToThisColumn.columnTo - cellThatBelongsToThisColumn.columnFrom;
    return <td colSpan={colSpan}>
      {
        'hypNode' in cellThatBelongsToThisColumn ?
          <div className={`hypothesis -hint ${!props.highlights || props.highlights.hypIds.includes(cellThatBelongsToThisColumn.hypNode.id) ? "" : "-faded"}`}>
            <Hint>{cellThatBelongsToThisColumn}</Hint>
            <span className="name">{cellThatBelongsToThisColumn.hypNode.name}</span>: {cellThatBelongsToThisColumn.hypNode.text}
          </div> :
          <div className={`tactic -hint ${colSpan > 1 ? "-spans-multiple-hypotheses" : ""}`}>
            <Hint>{cellThatBelongsToThisColumn}</Hint>
            {cellThatBelongsToThisColumn.tactic.text}
          </div>
      }
    </td>
  } else {
    return null;
  }
}

interface TableComponentProps {
  tabledCells: TabledCell[];
  highlights: Highlights;
}

const TableComponent = (props: TableComponentProps) => {
  const maxRow = Math.max(...props.tabledCells.map(hyp => hyp.row));
  const rows = Array.from({length: maxRow + 1}, (_, i) => i);

  const maxColumn = Math.max(...props.tabledCells.map(hyp => hyp.columnTo));
  const columns = Array.from({length: maxColumn + 1}, (_, i) => i);

  return (
    <table>
      <tbody>
        {rows.map((rowIndex) => (
          <tr key={rowIndex}>
            {columns.map((columnIndex) =>
              <TableCell key={columnIndex} columnIndex={columnIndex} rowIndex={rowIndex} tabledCells={props.tabledCells} highlights={props.highlights}/>
            )}
          </tr>
        ))}
      </tbody>
    </table>
  );
};

const getDirectChildHypsInThisBox = (proofTree: ConvertedProofTree, hypLayers: HypNode[][], hypNodeId: string) : string[] => {
  for (const tactic of proofTree.tactics) {
    const relevantHypArrow = tactic.hypArrows.find((hypArrow) => hypArrow.fromId === hypNodeId);
    if (relevantHypArrow) {
      const directChildIds = relevantHypArrow.toIds;
      const directChildIdsInThisBox = directChildIds.filter((directChildId) =>
        hypLayers.flat().find((hypNode) => hypNode.id === directChildId)
      );
      return directChildIdsInThisBox;
    }
  }
  return []
}

const getChildrenWidth = (proofTree: ConvertedProofTree, hypLayers: HypNode[][], hypNodeId: string) : number => {
  const directChildIds : string[] = getDirectChildHypsInThisBox(proofTree, hypLayers, hypNodeId);

  // base case
  if (directChildIds.length === 0) {
    return 1;
  // recursive case
  } else {
    let width = 0;
    directChildIds.forEach((childId) => {
      width += getChildrenWidth(proofTree, hypLayers, childId)
    });
    return width;
  }
}

const getChildIndex = (proofTree: ConvertedProofTree, parentHyp: HypNode, childHyp: HypNode) : number => {
  for (const tactic of proofTree.tactics) {
    const hypArrow = tactic.hypArrows.find((hypArrow) => hypArrow.fromId === parentHyp.id);
    if (hypArrow) {
      return hypArrow.toIds.findIndex((toId) => toId === childHyp.id);
    }
  }
  // Shouldn't really be called ever
  return 0;
}

export default (props: Props) => {
  const tabledHyps : TabledHyp[] = [];
  let maxColumn = 0;
  props.hypLayers.forEach((hypLayer, hypLayerIndex) => {
    hypLayer.forEach((hypNode) => {
      const tabledHypAbove : TabledHyp | undefined = getHypAbove(props.proofTree, tabledHyps, hypNode);
      
      const childrenWidth = getChildrenWidth(props.proofTree, props.hypLayers, hypNode.id);
      // "under something" hyps
      if (tabledHypAbove) {
        const childIndex = getChildIndex(props.proofTree, tabledHypAbove.hypNode, hypNode);
        const columnFrom = childIndex + tabledHypAbove.columnFrom;
        tabledHyps.push({
          hypNode,
          columnFrom,
          columnTo: columnFrom + childrenWidth,
          row: hypLayerIndex
        });
      // "intro" hyps
      } else {
        tabledHyps.push({
          hypNode,
          columnFrom: maxColumn,
          columnTo: maxColumn + childrenWidth,
          row: hypLayerIndex
        });
        maxColumn = maxColumn + childrenWidth + 1;
      }
    });
  });

  const tabledTactics : TabledTactic[] = [];
  let currentRow = 0;
  props.hypLayers.forEach((hypLayer, hypLayerIndex) => {
    const tactic : Tactic = whichTacticBirthedThisHypothesis(props.proofTree, hypLayer[0]!);
    const relevantTabledHyps = tabledHyps
    .filter((tabledHyp) => hypLayer.find((hypNode) => hypNode.id === tabledHyp.hypNode.id));
    const columnFrom = Math.min(
      ...relevantTabledHyps.map((tabledHyp) => tabledHyp.columnFrom)
    );
    const columnTo = Math.max(
      ...relevantTabledHyps.map((tabledHyp) => tabledHyp.columnTo)
    );
    tabledTactics.push({
      tactic,
      columnFrom,
      columnTo: columnTo,
      row: currentRow
    });
    relevantTabledHyps.forEach((tabledHyp) => tabledHyp.row = currentRow + 1);
    currentRow += 2;
  });

  return <TableComponent tabledCells={[...tabledHyps, ...tabledTactics]} highlights={props.highlights}/>
}


