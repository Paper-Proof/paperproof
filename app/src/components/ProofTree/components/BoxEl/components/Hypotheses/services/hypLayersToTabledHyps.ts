import { ConvertedProofTree, HypNode, Tactic, TabledHyp, TabledTactic, Box } from "types";

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

const getDirectChildHypsInThisBox = (proofTree: ConvertedProofTree, hypLayers: Box['hypLayers'], hypNodeId: string) : string[] => {
  for (const tactic of proofTree.tactics) {
    const relevantHypArrow = tactic.hypArrows.find((hypArrow) => hypArrow.fromId === hypNodeId);
    if (relevantHypArrow) {
      const directChildIds = relevantHypArrow.toIds;
      const directChildIdsInThisBox = directChildIds.filter((directChildId) =>
        hypLayers.map((hypLayer) => hypLayer.hypNodes).flat().find((hypNode) => hypNode.id === directChildId)
      );
      return directChildIdsInThisBox;
    }
  }
  return [];
}

const getChildrenWidth = (proofTree: ConvertedProofTree, hypLayers: Box['hypLayers'], hypNodeId: string) : number => {
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

const getChildrenWidths = (proofTree: ConvertedProofTree, hypLayers: Box['hypLayers'], hypNodeIds: string[]) : number => {
  let sum = 0;
  hypNodeIds.forEach((hypNodeId) => {
    sum += getChildrenWidth(proofTree, hypLayers, hypNodeId);
  });
  return sum;
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

const findHyp = (proofTree: ConvertedProofTree, hypId: string) => {
  proofTree.boxes.forEach((box) => {
    box.hypLayers.forEach((l) => {
      l.hypNodes.forEach((hypNode) => {
        if (hypNode.id === hypId) {
          return hypNode;
        }
      });
    });
  });
}

const hypLayersToTabledCells = (hypLayers : Box['hypLayers'], proofTree: ConvertedProofTree) => {
  const tabledHyps : TabledHyp[] = [];
  const tabledTactics : TabledTactic[] = [];

  let maxColumn = 0;
  let currentRow = 0;
  hypLayers.forEach((hypLayer, hypLayerIndex) => {
    const tactic : Tactic = proofTree.tactics.find((tactic) => tactic.id === hypLayer.tacticId)!;
    tactic.hypArrows.forEach((tacticShard) => {

      const parentHyp = tabledHyps.find((tabledHyp) => tabledHyp.hypNode.id === tacticShard.fromId);

      const columnFrom = parentHyp ? parentHyp.columnFrom : maxColumn;
      const allChildrenWidths = getChildrenWidths(proofTree, hypLayers, tacticShard.toIds);

      tabledTactics.push({
        tactic,
        columnFrom,
        columnTo: columnFrom + allChildrenWidths,
        row: currentRow
      });

      let hypColumnFrom = columnFrom;
      tacticShard.toIds.forEach((toId) => {
        const hypNode = hypLayer.hypNodes.find((hypNode) => hypNode.id === toId)!;
        const childrenWidth = getChildrenWidth(proofTree, hypLayers, toId);
        tabledHyps.push({
          hypNode,
          columnFrom: hypColumnFrom,
          columnTo: hypColumnFrom + childrenWidth,
          row: currentRow + 1
        });
        hypColumnFrom += childrenWidth;
      });
    });
    currentRow += 2;
  });

  // let maxColumn = 0;
  // hypLayers.forEach((hypLayer, hypLayerIndex) => {
  //   hypLayer.hypNodes.forEach((hypNode) => {
  //     const tabledHypAbove : TabledHyp | undefined = getHypAbove(proofTree, tabledHyps, hypNode);
  
  //     const childrenWidth = getChildrenWidth(proofTree, hypLayers, hypNode.id);
  //     // "under something" hyps
  //     if (tabledHypAbove) {
  //       const childIndex = getChildIndex(proofTree, tabledHypAbove.hypNode, hypNode);
  //       const columnFrom = childIndex + tabledHypAbove.columnFrom;
  //       tabledHyps.push({
  //         hypNode,
  //         columnFrom,
  //         columnTo: columnFrom + childrenWidth,
  //         row: hypLayerIndex
  //       });
  //     // "intro" hyps
  //     } else {
  //       tabledHyps.push({
  //         hypNode,
  //         columnFrom: maxColumn,
  //         columnTo: maxColumn + childrenWidth,
  //         row: hypLayerIndex
  //       });
  //       maxColumn = maxColumn + childrenWidth + 1;
  //     }
  //   });
  // });

  // const tabledTactics : TabledTactic[] = [];
  // let currentRow = 0;
  // hypLayers.forEach((hypLayer, hypLayerIndex) => {
  //   const tactic : Tactic = proofTree.tactics.find((tactic) => tactic.id === hypLayer.tacticId)!;
  //   const relevantTabledHyps = tabledHyps
  //     .filter((tabledHyp) => hypLayer.hypNodes.find((hypNode) => hypNode.id === tabledHyp.hypNode.id));
  //   const columnFrom = Math.min(
  //     ...relevantTabledHyps.map((tabledHyp) => tabledHyp.columnFrom)
  //   );
  //   const columnTo = Math.max(
  //     ...relevantTabledHyps.map((tabledHyp) => tabledHyp.columnTo)
  //   );
  //   tabledTactics.push({
  //     tactic,
  //     columnFrom,
  //     columnTo: columnTo,
  //     row: currentRow
  //   });
  //   relevantTabledHyps.forEach((tabledHyp) => tabledHyp.row = currentRow + 1);
  //   currentRow += 2;
  // });
  
  return [...tabledHyps, ...tabledTactics];
}

export default hypLayersToTabledCells;
