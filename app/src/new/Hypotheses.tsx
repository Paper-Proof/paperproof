import React from "react";

import { ConvertedProofTree, Box, HypNode } from "types";
import BoxEl from "./BoxEl";
import Hint from "./Hint";

interface Props {
  proofTree: ConvertedProofTree;
  hypLayers: HypNode[][];
}

const getHypothesisTacticBefore = (proofTree: ConvertedProofTree, hypNodeRow: HypNode[]) => {
  const hypNodeId = hypNodeRow[0]!.id;
  const tactic = proofTree.tactics.find((tactic) => tactic.hypArrows.find((hypArrow) => hypArrow.toIds.includes(hypNodeId)));
  return tactic;
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
  columnTo : number,
  row : number;
}

function isBetween(num, range) {
  return num >= Math.min(...range) && num <= Math.max(...range);
}

const TableCell = ({ rowIndex, columnIndex, tabledHyps }: { rowIndex : number, columnIndex: number, tabledHyps: TabledHyp[] }) => {
  const tabledHypsOnThisRow = tabledHyps.filter((tabledHyp) => tabledHyp.row === rowIndex);

  const hypThatBelongsToThisColumn = tabledHypsOnThisRow
  .find((hyp) =>
  isBetween(columnIndex, [hyp.columnFrom, hyp.columnTo - 1])
  );
  if (!hypThatBelongsToThisColumn) {
    return <td/>
  } else if (hypThatBelongsToThisColumn.columnFrom === columnIndex) {
    return <td colSpan={hypThatBelongsToThisColumn.columnTo - hypThatBelongsToThisColumn.columnFrom}>
      <div className="hypothesis -hint">
        <Hint>{hypThatBelongsToThisColumn.hypNode}</Hint>
        <span className="name">{hypThatBelongsToThisColumn.hypNode.name}</span>: {hypThatBelongsToThisColumn.hypNode.text}
      </div>
    </td>
  } else {
    return null;
  }
}

const TableComponent = ({ tabledHyps }: { tabledHyps: TabledHyp[] }) => {
  const maxRow = Math.max(...tabledHyps.map(hyp => hyp.row));
  const rows = Array.from({length: maxRow + 1}, (_, i) => i);

  const maxColumn = Math.max(...tabledHyps.map(hyp => hyp.columnTo));
  const columns = Array.from({length: maxColumn + 1}, (_, i) => i);

  return (
    <table>
      <tbody>
        {rows.map((rowIndex) => (
          <tr key={rowIndex}>
            {columns.map((columnIndex) =>
              <TableCell columnIndex={columnIndex} rowIndex={rowIndex} tabledHyps={tabledHyps}/>
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

  console.log({ tabledHyps });

  return <TableComponent tabledHyps={tabledHyps}/>




  // const tactic = getHypothesisTacticBefore(props.proofTree, props.hypNodeRow);
  // return <div className="hypothesis-row">
  //   {
  //     tactic &&
  //     props.proofTree.boxes.filter((box) => tactic.haveBoxIds.includes(box.id))
  //     .map((haveBox) =>
  //       <BoxEl proofTree={props.proofTree} depth={props.depth + 1} box={haveBox}/>
  //     )
  //   }
  //   {
  //     tactic &&
  //     <div className={`tactic -hint ${(tactic.hypArrows[0].fromId === null && tactic.haveBoxIds.length === 0) ? "-with-margin-top" : ""}`}>
  //       <Hint>{tactic}</Hint>
  //       {tactic?.text}
  //     </div>
  //   }
  //   <div className="hypotheses">
  //     {props.hypNodeRow.map((hypNode) =>
  //       <div key={hypNode.id} className="hypothesis -hint">
  //         <Hint>{{hypNode}}</Hint>
  //         <span className="name">{hypNode.name}</span>: {hypNode.text}
  //       </div>
  //     )}
  //   </div>
  // </div>
}
