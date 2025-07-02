import { ConvertedProofTree, Tactic, TabledHyp, Box, HypNode, Table, HypLayer } from "types";

const getDirectChildHypsInThisBox = (proofTree: ConvertedProofTree, hypLayers: Box['hypLayers'], hypNodeId: string) : string[] => {
  for (const hypLayer of hypLayers) {
    const tactic = proofTree.tactics.find((tactic) => tactic.id === hypLayer.tacticId)!;
    const tacticShard = tactic.hypArrows.find((shard) => shard.fromId === hypNodeId);
    if (tacticShard) return tacticShard.toIds;
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

const doAnyLayersBelowHaveParentsAbove = (hypLayers: Box['hypLayers'], hypLayerIndex: number, proofTree: ConvertedProofTree) : boolean => {
  const hypLayersAbove = hypLayers.slice(0, hypLayerIndex);
  const hypLayersBelow = hypLayers.slice(hypLayerIndex);
  return hypLayersBelow.some((hypLayer) => {
    const tactic : Tactic = proofTree.tactics.find((tactic) => tactic.id === hypLayer.tacticId)!;
    return tactic.hypArrows.some((tacticShard) => {
      return hypLayersAbove.some((hypLayer) => {
        const parent = hypLayer.hypNodes.find((hypNode) => hypNode.id === tacticShard.fromId);
        return parent ? true : false;
      });
    });
  });
}

const getTabledHypFromTables = (tables : Table[], hypId: string | null) : TabledHyp | undefined => {
  if (hypId === null) return undefined;
  const tabledHyps = tables.map((table) => table.tabledHyps).flat();
  return tabledHyps.find((tabledHyp) => tabledHyp.hypNode.id === hypId);
}

const isHypChildless = (proofTree: ConvertedProofTree, hypNodeId: string) : boolean => {
  const hasChildren = proofTree.tactics.some((tactic) =>
    tactic.hypArrows.some((hypArrow) => hypArrow.fromId === hypNodeId)
  )
  return !hasChildren
}

const partitionHypsIntoRow1AndRow2 = (proofTree: ConvertedProofTree, initLayer: HypLayer, isSingleTacticMode: boolean): [HypNode[], HypNode[]] => {
  const row1Hyps : HypNode[] = [];
  const row2Hyps : HypNode[] = [];
  initLayer.hypNodes.forEach((hypNode : HypNode) => {
    const isRow1 = isSingleTacticMode ?
      isHypChildless(proofTree, hypNode.id) :
      hypNode.isProof === "data" && isHypChildless(proofTree, hypNode.id)
    if (isRow1) {
      row1Hyps.push(hypNode);
    } else {
      row2Hyps.push(hypNode);
    }
  });
  return [row1Hyps, row2Hyps]
}

const hypsToTables = (hypLayers : Box['hypLayers'], proofTree: ConvertedProofTree, isSingleTacticMode: boolean) : Table[] => {
  const tables : Table[] = [];
  let currentTable : Table = tables[tables.length - 1];

  hypLayers.forEach((hypLayer, hypLayerIndex) => {
    const tactic : Tactic = proofTree.tactics.find((tactic) => tactic.id === hypLayer.tacticId)!;
    let thisLayerHypNodes : HypNode[] = hypLayer.hypNodes;

    // Start a new table if this is the "init" tactic!
    if (tactic.text === "init") {
      const [row1Hyps, row2Hyps] = partitionHypsIntoRow1AndRow2(proofTree, hypLayer, isSingleTacticMode)
      thisLayerHypNodes = row2Hyps;
      tables.push({ tabledHyps: [], tabledTactics: [], currentRow: 0, row1Hyps });
      currentTable = tables[tables.length - 1];
    }
    // Start a new table if none of the hypotheses inherit from each other!
    else if (!doAnyLayersBelowHaveParentsAbove(hypLayers, hypLayerIndex, proofTree)) {
      tables.push({ tabledHyps: [], tabledTactics: [], currentRow: 0 });
      currentTable = tables[tables.length - 1];
    }

    // Some tactic shards are outside the box we're currently drawing
    const interestingTacticShards = tactic.hypArrows.filter((tacticShard) =>
      tacticShard.toIds.some((toId) =>
        thisLayerHypNodes.map((hypNode) => hypNode.id).includes(toId)
      )
    );
    interestingTacticShards.forEach((tacticShard) => {
      const parentHyp = getTabledHypFromTables(tables, tacticShard.fromId);

      const maxColumn = Math.max(...currentTable.tabledHyps.map((hyp) => hyp.columnTo), 0);
      const columnFrom = parentHyp ? parentHyp.columnFrom : maxColumn;
      const allChildrenIds = tacticShard.toIds.filter((id) => thisLayerHypNodes.find((hypNode) => hypNode.id === id));
      const allChildrenWidths = getChildrenWidths(proofTree, hypLayers, allChildrenIds);

      // Drawing parent arrows.
      // 1. Do we have a parent that's in another window? Draw an arrow.
      // 2. Do we have a parent that's multiple rows above us? Draw an arrow.
      let arrowFrom = null;
      if (!parentHyp || currentTable.currentRow - parentHyp.row > 2) {
        arrowFrom = tacticShard.fromId;
      }

      currentTable.tabledTactics.push({
        type: "tactic",
        tactic,
        columnFrom,
        columnTo: columnFrom + allChildrenWidths,
        row: currentTable.currentRow,
        arrowFrom,
        shardId: tacticShard.shardId
      });

      let hypColumnFrom = columnFrom;
      tacticShard.toIds.forEach((toId) => {
        const hypNode = thisLayerHypNodes.find((hypNode) => hypNode.id === toId)!;
        // This shouldn't happen as far as I'm aware, but can be investigated in the converter. 
        if (!hypNode) return

        const childrenWidth = getChildrenWidth(proofTree, hypLayers, toId);
        currentTable.tabledHyps.push({
          type: "hypothesis",
          hypNode,
          columnFrom: hypColumnFrom,
          columnTo: hypColumnFrom + childrenWidth,
          row: currentTable.currentRow + 1
        });
        hypColumnFrom += childrenWidth;
      });
    });
    currentTable.currentRow += 2;
  });

  return tables;
}

export default hypsToTables;
