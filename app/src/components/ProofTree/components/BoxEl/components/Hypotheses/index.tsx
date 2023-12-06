import React from "react";

import { ConvertedProofTree, Box, HypNode, Tactic, Highlights, TabledHyp, TabledTactic } from "types";
import BoxEl from "../..";
import Table from "./components/Table";

interface Props {
  proofTree: ConvertedProofTree;
  hypLayers: HypNode[][];
  highlights: Highlights;
}

const whichTacticBirthedThisHypothesis = (proofTree: ConvertedProofTree, hypNode: HypNode) : Tactic => {
  const tactic = proofTree.tactics.find((tactic) => tactic.hypArrows.find((hypArrow) => hypArrow.toIds.includes(hypNode.id)));
  return tactic || { text: "init", id: "666", dependsOnIds: [], goalArrows: [], hypArrows: [], haveBoxIds: [] };
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

const HypothesesComponent = (props: Props) => {
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

  return <Table proofTree={props.proofTree} tabledCells={[...tabledHyps, ...tabledTactics]} highlights={props.highlights}/>
}

export default HypothesesComponent;
