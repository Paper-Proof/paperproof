import { TLParentId, createShapeId } from "@tldraw/tldraw";

import { UIHypTree, UIElement, UIIdElement, HypLayer, Window, UIShared } from "types";

import getHypNodeText from '../getHypNodeText';
import hStack from '../hStack';
import vStack from '../vStack';
import byLevel from '../byLevel';
import sum from '../sum';
import getTreeWidth from '../getTreeWidth';
import withWidth from '../withWidth';

import createNode from './createNode';
import createWindow from './createWindow';

import CreateId from '../CreateId';

const createEmpty = (): UIElement => {
  return {
    size: [0, 0],
    draw: () => { }
  }
}

const createTrees = (hMargin: number, trees: UIHypTree[]): UIElement => {
  if (trees.length == 0) {
    return createEmpty();
  }
  const rowHeights = byLevel(hMargin, trees).map(row => hStack(hMargin, row).size[1]);
  const colWidths = trees.map(t => getTreeWidth(hMargin, t));
  function draw(x: number, y: number, level: number, t: UIHypTree): void {
    if (level < t.level) {
      draw(x, y + rowHeights[level], level + 1, t);
      return;
    }
    const x0 = x;
    let lastNodeX = x;
    for (const node of t.nodes) {
      node.node.draw(x, y + t.tactic.size[1]);
      lastNodeX = x + node.node.size[0];
      const widths = [node.node.size[0]];
      if (node.tree) {
        draw(x, y + rowHeights[level], level + 1, node.tree);
        widths.push(getTreeWidth(hMargin, node.tree));
      }
      x += Math.max(...widths) + hMargin;
    }
    // We know the preffered width of the tactic only after we draw all the nodes (and their subtrees).
    // This is for cases like `match` or `induction` where the tactic should span all the underlying nodes.
    t.tactic.draw(x0, y, lastNodeX - x0);
  }
  return {
    size: [
      sum(colWidths, hMargin),
      sum(rowHeights)
    ],
    draw: (x, y) => {
      for (const tree of trees) {
        draw(x, y, 0, tree);
        x += getTreeWidth(hMargin, tree) + hMargin;
      }
    }
  };
}

const createWindowInsides = (shared: UIShared, parentId: TLParentId | undefined, window: Window, depth: number): UIElement => {
  let rows: UIElement[] = [];

  // 1. Draw all hypothesis nodes (and their tactic nodes)
  // Layers of hypNodes can have series of `rw` tactics where
  // we should attempt to stack nodes with the same name together.
  // We will assume that nodes in the same layer are generated by
  // the same tactic.
  function hasCommonNodes(as: HypLayer[], b: HypLayer) {
    const lastLayer = as[as.length - 1];
    const prevIds = shared.proofTree.tactics.flatMap(t => t.hypArrows.flatMap(a => b.some(toNode => a.toIds.includes(toNode.id)) && a.fromId ? a.fromId : []));
    return lastLayer.some(n => prevIds.includes(n.id));
  }
  const rwSeqs: HypLayer[][] = [];
  for (const layer of window.hypNodes) {
    if (rwSeqs.length > 0 && hasCommonNodes(rwSeqs[rwSeqs.length - 1], layer)) {
      rwSeqs[rwSeqs.length - 1].push(layer);
    } else {
      rwSeqs.push([layer]);
    }
  }
  // Have window can only be at the top level (since it never destructs anything but each tactic after first in rwSeq does).
  for (const rwSeq of rwSeqs) {
    const topLevelTrees = new Set<UIHypTree>();
    const nodeToTree = new Map<string, UIHypTree>();
    for (let level = rwSeq.length - 1; level >= 0; level--) {
      const layer = rwSeq[level];
      const layerTactics = shared.proofTree.tactics
        .filter(tactic =>
          tactic.hypArrows.some(hypArrow =>
            layer.some(nodeAfter => hypArrow.toIds.includes(nodeAfter.id))
          )
        );
      if (layerTactics.length == 0) {
        // This is a weird case for the top level hypothesis which aren't generated by tactics. 
        topLevelTrees.add({
          tactic: createEmpty(), level, nodes: layer.map(
            node => {
              const hypNode = createNode(shared, parentId, getHypNodeText(node), "hypothesis", CreateId.node(node.id));
              const tree = nodeToTree.get(node.id);
              if (tree) {
                topLevelTrees.delete(tree);
              }
              return { id: node.id, node: hypNode, tree };
            }
          )
        });
      }
      for (const tactic of layerTactics) {
        tactic.hypArrows.forEach((hypArrow) => {
          const nodesAfter = layer
            .filter((nodeAfter) => hypArrow.toIds.includes(nodeAfter.id))
            .filter(n => shared.uiConfig.hideNulls ? !n.id.includes("null") : true);
          if (nodesAfter.length === 0) {
            return;
          }

          const tacticNode = createNode(
            shared,
            parentId,
            tactic.text,
            "tactic",
            CreateId.hypTactic(tactic.id, hypArrow.fromId, window.id)
          );

          const haveWindows = tactic.haveWindowIds
            .flatMap(
              (id) => shared.proofTree.windows.find((w) => w.id === id) ?? []
            )
            .map((w) => createWindow(shared, parentId, w, depth + 1));
          const hTree: UIHypTree = {
            tactic: vStack(0, [hStack(shared.inBetweenMargin, haveWindows), tacticNode]),
            level,
            nodes: nodesAfter.map(
              node => {
                const hypNode = createNode(shared, parentId, getHypNodeText(node), "hypothesis", CreateId.node(node.id));
                const tree = nodeToTree.get(node.id);
                if (tree) {
                  topLevelTrees.delete(tree);
                }
                return { id: node.id, node: hypNode, tree };
              }
            )
          }
          if (hypArrow.fromId) {
            nodeToTree.set(hypArrow.fromId, hTree)
          }
          topLevelTrees.add(hTree);
        });
      }
    }
    if (topLevelTrees.size > 0) {
      // Reverse because we were adding them bottom up but should prefer those which start earlier.
      rows.push(createTrees(shared.inBetweenMargin, Array.from(topLevelTrees.values()).reverse()));
    }
  }

  // 2. Draw all child windows
  const subWindows = shared.proofTree.windows.filter((w) => w.parentId == window.id);
  const frameEls: UIElement[] = subWindows.map((subWindow) =>
    createWindow(shared, parentId, subWindow, depth + 1)
  );

  let windowWidth = 0;

  // 3. Draw all goal nodes (and their tactic nodes)
  const goalNodes = [...window.goalNodes].reverse();
  // let goalEls : UIIdElement[] = [];
  let goalAndTacticEls : UIElement[] = [];
  goalNodes.forEach((goalNode) => {
    const goalEl: UIIdElement = withWidth(() => windowWidth, createNode(shared, parentId, goalNode.text, "goal", CreateId.node(goalNode.id))) as UIIdElement;

    const tactic = shared.proofTree.tactics.find((tactic) =>
      tactic.goalArrows.some((a) => a.fromId === goalNode.id) ||
      tactic.successGoalId === goalNode.id
    );
    let tacticEl : UIElement;
    if (tactic) {
      const isSuccessTactic = tactic.successGoalId && tactic.text !== "sorry";
      tacticEl = createNode(shared, parentId, (isSuccessTactic ? `🎉 ${tactic.text} 🎉` : tactic.text), "tactic", CreateId.goalTactic(tactic.id));
    } else {
      tacticEl = createNode(shared, parentId, "...", "tactic", createShapeId());
    }
    const isLastGoalNode = (tactic && tactic.successGoalId && tactic.text !== "sorry") || !tactic;
    if (isLastGoalNode) {
      goalAndTacticEls.push(withWidth(() => windowWidth, tacticEl), goalEl);
    } else {
      goalAndTacticEls.push(tacticEl, goalEl);
    }
  });

  if (frameEls.length > 0) {
    // In such case we want to attach last tactic to the row with frames
    const framesEl = hStack(shared.inBetweenMargin, frameEls);
    // We can assume that the first element is a tactic since we have frames.
    rows.push(vStack(0, [framesEl, withWidth(framesEl.size[0], goalAndTacticEls[0]), ...goalAndTacticEls.slice(1)]));
  } else {
    const goals = vStack(0, goalAndTacticEls);
    rows.push(goals);
  }

  // ***EXPERIMENTAL*** (everything with this variable is experimental)
  // Make goal nodes always span 100% width
  windowWidth = Math.max(...rows.map((b) => b.size[0]));
  // ***EXPERIMENTAL***

  return vStack(shared.inBetweenMargin, rows);
}

export default createWindowInsides;
