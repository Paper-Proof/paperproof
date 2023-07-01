import { App, TLParentId, TLShapeId } from "@tldraw/tldraw";

import { HypTree, Element, IdElement, HypNode, HypLayer, Window, Format, UiConfig } from "../types";

import getHypNodeText from './services/getHypNodeText';
import hStack from './services/hStack';
import vStack from './services/vStack';
import byLevel from './services/byLevel';
import sum from './services/sum';
import getTreeWidth from './services/getTreeWidth';
import getTextSize from './services/getTextSize';

function emptyEl(): Element {
  return { size: [0, 0], draw: () => { } };
}

function trees(hMargin: number, ...trees: HypTree[]): Element {
  if (trees.length == 0) return { size: [0, 0], draw: () => { } };
  const rowHeights = byLevel(hMargin, trees).map(row => hStack(hMargin, ...row).size[1]);
  const colWidths = trees.map(t => getTreeWidth(hMargin, t));
  function draw(x: number, y: number, level: number, t: HypTree) : void {
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

function shouldHide(node: HypNode, uiConfig: UiConfig) {
  return uiConfig.hideNulls ? node.id.includes("null") : false;
}

export function buildProofTree(app: App, proofTree: Format, currentGoal: string, uiConfig: UiConfig) {
  app.updateInstanceState({ isFocusMode: true });

  const inBetweenMargin = 20;
  const framePadding = 20;

  const { tactics } = proofTree;

  const shapeMap = new Map<string, TLShapeId>();

  function drawArrow(from: TLShapeId, to: TLShapeId) {
    app.createShapes([
      {
        id: app.createShapeId(),
        type: "customArrow",
        props: {
          start: {
            type: 'binding', boundShapeId: from,
            normalizedAnchor: { x: 0.5, y: 1 },
            isExact: true
          },
          end: {
            type: 'binding', boundShapeId: to,
            normalizedAnchor: { x: 0.5, y: 0 },
            isExact: true
          },
          color: "grey",
        },
      },
    ]);
  }

  const createNode = (
    parentId: TLParentId | undefined,
    text: string,
    type: "value" | "tactic" | "redvalue" = "value",
    // This is for arrows
    externalId: string,
    ids: string[] = [],
  ): IdElement => {
    const id = app.createShapeId();
    shapeMap.set(externalId, id);
    const [w, h] = getTextSize(app, text);
    return {
      id,
      size: [w, h],
      draw(x, y, prefferedWidth?: number) {
        const isCurrentGoal = ids.includes(currentGoal);
        const effectiveW = !!prefferedWidth && prefferedWidth > w ? prefferedWidth : w;
        app.createShapes([
          {
            id,
            type: "geo",
            x,
            y,
            parentId,
            props: {
              geo: "rectangle",
              // Here we write just 'mono' but in measure text we need to write the actual font family.
              font: "mono",
              w: effectiveW,
              h,
              ...(type == "value"
                ? { dash: "solid", fill: "solid", color: "light-green" }
                : type == "redvalue"
                  ? (
                    isCurrentGoal ?
                    { dash: "solid", fill: "solid", color: "red" } :
                    { dash: "solid", fill: "solid", color: "light-red" }
                  )
                  : { dash: "dotted", fill: "none", color: "grey" }),
              size: "m",
              text,
            },
          },
        ]);
      }
    }
  };

  function withPadding(padding: { left: number, right: number, top: number, bottom: number }, el: Element): Element {
    return {
      size: [el.size[0] + padding.left + padding.right, el.size[1] + padding.top + padding.bottom],
      draw: (x, y) => {
        el.draw(x + padding.left, y + padding.top);
      }
    }
  }

  function withWidth(width: number, el: Element): Element {
    return { ...el, draw: (x, y) => { el.draw(x, y, width); } }
  }

  const createWindow = (parentId: TLParentId | undefined, window: Window, format: Format, depth: number): Element => {
    const frameId = app.createShapeId();
    const nodes = withPadding({ left: framePadding, right: framePadding, top: framePadding, bottom: 0 },
      createNodes(frameId, window, format, depth));
    const title = createNode(frameId, window.goalNodes[0].name, "tactic", "");
    const layout = vStack(0, nodes, withWidth(nodes.size[0], title));
    const [w, h] = layout.size;

    const draw = (x: number, y: number) => {
      app.createShapes([
        {
          id: frameId,
          type: "window",
          x,
          y,
          parentId,
          props: { name: window.id, w, h, depth },
        },
      ]);
      layout.draw(0, 0);
    };
    return { size: [w, h], draw };
  }

  app.selectAll().deleteShapes();

  const arrowsToDraw: ({ fromId: string, toShapeId: TLShapeId } | { fromShapeId: TLShapeId, toId: string })[] = [];

  function createNodes(
    parentId: TLParentId | undefined,
    window: Window,
    format: Format,
    depth: number
  ): Element {
    let rows: Element[] = [];
    // Layers of hypNodes can have series of `rw` tactics where
    // we should attempt to stack nodes with the same name together.
    // We will assume that nodes in the same layer are generated by
    // the same tactic.
    function hasCommonNodes(as: HypLayer[], b: HypLayer) {
      const lastLayer = as[as.length - 1];
      const prevIds = format.tactics.flatMap(t => t.hypArrows.flatMap(a => b.some(toNode => a.toIds.includes(toNode.id)) && a.fromId ? a.fromId : []));
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
    // Have window can only be at the top level (since it never desctructs anything but each tactic after first in rwSeq does).
    for (const rwSeq of rwSeqs) {
      const topLevelTrees = new Set<HypTree>();
      const nodeToTree = new Map<string, HypTree>();
      for (let level = rwSeq.length - 1; level >= 0; level--) {
        const layer = rwSeq[level];
        const layerTactics = format.tactics
          .filter(tactic =>
            tactic.hypArrows.some(hypArrow =>
              layer.some(nodeAfter => hypArrow.toIds.includes(nodeAfter.id))
            )
          );
        if (layerTactics.length == 0) {
          // This is a weird case for the top level hypothesis which aren't generated by tactics. 
          topLevelTrees.add({
            tactic: emptyEl(), level, nodes: layer.map(
              node => {
                const hypNode = createNode(parentId, getHypNodeText(node), 'value', node.id);
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
              .filter(n => !shouldHide(n, uiConfig));
            if (nodesAfter.length === 0) {
              return;
            }

            const tacticNode = createNode(
              parentId,
              tactic.text,
              "tactic",
              `${tactic.id}${hypArrow.fromId}${parentId}`,
            );
            if (hypArrow.fromId) {
              arrowsToDraw.push({ fromId: hypArrow.fromId, toShapeId: tacticNode.id });
            }
            arrowsToDraw.push(...nodesAfter.map(n => ({ fromShapeId: tacticNode.id, toId: n.id })));
            const haveWindows = format.windows
              .filter(w => tactic.haveWindowId === w.id)
              .map(w => createWindow(parentId, w, format, depth + 1));
            const hTree: HypTree = {
              tactic: vStack(0, hStack(inBetweenMargin, ...haveWindows), tacticNode), level, nodes: nodesAfter.map(
                node => {
                  const hypNode = createNode(parentId, getHypNodeText(node), 'value', node.id);
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
        rows.push(trees(inBetweenMargin, ...[...topLevelTrees.values()].reverse()));
      }
    }
    const subWindows = format.windows.filter((w) => w.parentId == window.id);
    const frames: Element[] = [];
    for (const subWindow of subWindows) {
      frames.push(createWindow(parentId, subWindow, format, depth + 1));
    }
    const goalNodes = [...window.goalNodes].reverse();
    const proof: Element[] = goalNodes.flatMap(goalNode => {
      const tactic = tactics.find(
        (t) =>
          t.goalArrows.some((a) => a.fromId == goalNode.id) ||
          t.successGoalId == goalNode.id
      );
      const id = localStorage.getItem("dev") === 'true'
        ? ' ' + goalNode.id
        : '';
      const goalEl: Element = createNode(
        parentId,
        goalNode.text + id,
        "redvalue",
        goalNode.id,
        [goalNode.id]
      );
      return [tactic ?
        createNode(parentId,
          tactic.text + (tactic.successGoalId ? " 🎉" : ""),
          "tactic",
          tactic.id,
        )
        : [], goalEl].flat();
    });
    if (frames.length > 0) {
      // In such case we want to attach last tactic to the row with frames
      const framesEl = hStack(inBetweenMargin, ...frames);
      // We can assume that the first element is a tactic since we have frames.
      rows.push(vStack(0, framesEl, withWidth(framesEl.size[0], proof[0]), ...proof.slice(1)));
    } else {
      const goals = vStack(0, ...proof);
      rows.push(goals);
    }
    return vStack(inBetweenMargin, ...rows);
  }

  const root = proofTree.windows.find((w) => w.parentId == null);
  if (root) {
    const el = createWindow(undefined, root, proofTree, 0);
    el.draw(0, 0);
  }
  // Draw arrows
  for (const arrow of arrowsToDraw) {
    if ('fromId' in arrow) {
      const fromShapeId = shapeMap.get(arrow.fromId);
      if (fromShapeId) {
        drawArrow(fromShapeId, arrow.toShapeId)
      }
    } else {
      const toShapeId = shapeMap.get(arrow.toId);
      if (toShapeId) {
        drawArrow(arrow.fromShapeId, toShapeId);
      }
    }
  }
}

