import * as React from "react";
import { useState } from "react";
import { useEffect } from "react";
import * as ReactDOM from "react-dom";
import {
  App,
  LABEL_FONT_SIZES,
  TEXT_PROPS,
  TLParentId,
  TLShapeId,
  Tldraw,
  TldrawEditorConfig,
} from "@tldraw/tldraw";
import "@tldraw/tldraw/editor.css";
import "@tldraw/tldraw/ui.css";
import { toEdges } from "./converter";
import { WindowShape } from "./window";

const fontFamily = 'Menlo, Monaco, "Courier New", monospace;'

interface HypTree {
  level: number;
  tactic: Element;
  nodes: { node: Element, tree?: HypTree }[];
}

interface Element {
  size: [number, number];
  draw: (x: number, y: number) => void;
}

interface IdElement extends Element {
  id: TLShapeId;
}

function emptyEl(): Element {
  return { size: [0, 0], draw: () => { } };
}

function vStack(margin: number, ...boxes: Element[]): Element {
  if (boxes.length == 0) return { size: [0, 0], draw: () => { } };
  return {
    size: [
      Math.max(...boxes.map((b) => b.size[0])),
      boxes.map((b) => b.size[1]).reduce((x, y) => x + y) + (boxes.length - 1) * margin,
    ],
    draw(x, y) {
      let dy = 0;
      for (const box of boxes) {
        box.draw(x, y + dy);
        dy += box.size[1] + margin;
      }
    },
  };
}

// hStack aligns to the bottom
function hStack(margin: number, ...boxes: Element[]): Element {
  if (boxes.length == 0) return { size: [0, 0], draw: () => { } };
  const [w, h] = [
    boxes.map((b) => b.size[0]).reduce((x, y) => x + y) + (boxes.length - 1) * margin,
    Math.max(...boxes.map((b) => b.size[1])),
  ];
  return {
    size: [w, h],
    draw(x, y) {
      let dx = 0;
      for (const box of boxes) {
        box.draw(x + dx, y + h - box.size[1]);
        dx += box.size[0] + margin;
      }
    },
  };
}

function transpose(rows: Element[][]): Element[][] {
  if (rows.length == 0) return [];
  const cols: Element[][] = [];
  for (let i = 0; i < rows[0].length; i++) {
    cols.push(rows.map((row) => row[i]));
  }
  return cols;
}

function byLevel(hMargin: number, trees: HypTree[]): Element[][] {
  const rows: Element[][] = [];
  function visit(t: HypTree) {
    while (rows.length <= t.level) {
      rows.push([]);
    }
    rows[t.level].push(vStack(0, t.tactic, hStack(hMargin, ...t.nodes.map(n => n.node))));
    for (const n of t.nodes) {
      if (n.tree) {
        visit(n.tree);
      }
    }
  }
  trees.forEach(visit);
  return rows;
}

function sum(a: number[], margin: number = 0): number {
  if (a.length == 0) {
    return 0;
  }
  return a.reduce((x, y) => x + y, 0) + (a.length - 1) * margin;
}

function getTreeWidth(hMargin: number, t: HypTree): number {
  const widths = t.nodes.flatMap(n =>
    [Math.max(n.node.size[0], n.tree ? getTreeWidth(hMargin, n.tree) : 0)])
  return Math.max(t.tactic.size[0], sum(widths, hMargin));
}

function trees(hMargin: number, ...trees: HypTree[]): Element {
  if (trees.length == 0) return { size: [0, 0], draw: () => { } };
  const rowHeights = byLevel(hMargin, trees).map(row => hStack(hMargin, ...row).size[1]);
  const colWidths = trees.map(t => getTreeWidth(hMargin, t));
  function draw(x: number, y: number, level: number, t: HypTree) {
    if (level < t.level) {
      return draw(x, y + rowHeights[level], level + 1, t);
    }
    t.tactic.draw(x, y);
    for (const node of t.nodes) {
      node.node.draw(x, y + t.tactic.size[1]);
      const widths = [node.node.size[0]];
      if (node.tree) {
        draw(x, y + rowHeights[level], level + 1, node.tree);
        widths.push(getTreeWidth(hMargin, node.tree));
      }
      x += Math.max(...widths) + hMargin;
    }
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

function grid(vMargin: number, hMargin: number, ...rows: Element[][]): Element {
  if (rows.length == 0) return { size: [0, 0], draw: () => { } };
  const rowHeights = rows.map((row) => hStack(hMargin, ...row).size[1]);
  const colWidths = transpose(rows).map((col) => vStack(vMargin, ...col).size[0]);
  return {
    size: [
      colWidths.reduce((x, y) => x + y) + (colWidths.length - 1) * hMargin,
      rowHeights.reduce((x, y) => x + y) + (rowHeights.length - 1) * vMargin,
    ],
    draw(x0, y) {
      for (let i = 0; i < rows.length; i++) {
        let x = x0;
        for (let j = 0; j < rows[i].length; j++) {
          rows[i][j].draw(x, y);
          x += colWidths[j] + hMargin;
        }
        y += rowHeights[i] + vMargin;
      }
    }
  }
}

type Node = { text: string; id: string; name?: string; subNodes?: NodeLayer[] };

type NodeLayer = Node[];

interface GoalNode {
  text: string;
  id: string;
}

interface HypNode {
  text: string;
  name: string | null;
  id: string;
  haveWindowId?: number;
}

type HypLayer = HypNode[];

interface Window {
  id: number;
  parentId: number | null;
  goalNodes: GoalNode[];
  hypNodes: HypLayer[];
}

interface Tactic {
  id: string;
  text: string;
  dependsOnIds: string[];
  goalArrows: { fromId: string; toId: string }[];
  hypArrows: { fromId: string | null; toId: string }[];
  // hmm
  isSuccess: boolean | string;
  successGoalId?: string;
}

interface Format {
  windows: Window[];
  tactics: Tactic[];
}

const config = new TldrawEditorConfig({
  shapes: [WindowShape],
  allowUnknownShapes: true,
});

function getHypNodeText(node: HypNode) {
  const text = (() => {
    if (!node.name) {
      return node.text;
    }
    // For cases h._@.Examples._hyg.1162
    const hypName = node.name.includes(".")
      ? `${node.name.split(".")[0]}✝`
      : node.name;
    return `${hypName}: ${node.text}`;
  })();
  const devId = localStorage.getItem("dev") === 'true'
    ? ' ' + node.id
    : '';
  return `${text}${devId}`;
}

function render(app: App, proofTree: Format, currentGoal: string) {
  app.updateInstanceState({ isFocusMode: true });

  const inBetweenMargin = 20;
  const framePadding = 20;

  const { tactics } = proofTree;

  const shapeMap = new Map<string, TLShapeId>();

  function drawArrow(from: TLShapeId, to: TLShapeId) {
    app.createShapes([
      {
        id: app.createShapeId(),
        type: "arrow",
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
    const [w, h] = getTextSize(text);
    return {
      id,
      size: [w, h],
      draw(x, y) {
        const isCurrentGoal = ids.includes(currentGoal);
        app.createShapes([
          {
            id,
            type: "geo",
            x,
            y,
            parentId,
            props: {
              geo: "rectangle",
              font: "mono",
              w,
              h,
              ...(type == "value"
                ? { dash: "draw", fill: "solid", color: "light-green" }
                : type == "redvalue"
                  ? (
                    isCurrentGoal ? { dash: "draw", fill: "pattern", color: "light-blue" } :
                      { dash: "draw", fill: isCurrentGoal ? "pattern" : "solid", color: "light-red" }
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

  const createWindow = (parentId: TLParentId | undefined, window: Window, format: Format): Element => {
    const frameId = app.createShapeId();
    const nodes = createNodes(frameId, window, format);
    const [w, h] = [nodes.size[0] + 2 * framePadding, nodes.size[1] + 2 * framePadding];
    const draw = (x: number, y: number) => {
      app.createShapes([
        {
          id: frameId,
          type: "window",
          x,
          y,
          parentId,
          props: { name: window.id, w, h },
        },
      ]);
      nodes.draw(framePadding, framePadding);
    };
    return { size: [w, h], draw };
  }

  function getTextSize(text: string): [number, number] {
    const size = app.textMeasure.measureText({
      ...TEXT_PROPS,
      text,
      fontFamily: "mono",
      fontSize: LABEL_FONT_SIZES["m"],
      width: "fit-content",
      padding: "16px",
    });
    return [
      // Don't know how to calculate size correctly yet
      size.w * 1.6,
      size.h,
    ];
  }

  app.selectAll().deleteShapes();

  const arrowsToDraw: ({ fromId: string, toShapeId: TLShapeId } | { fromShapeId: TLShapeId, toId: string })[] = [];

  function createNodes(
    parentId: TLParentId | undefined,
    window: Window,
    format: Format
  ): Element {
    let rows: Element[] = [];
    // Layers of hypNodes can have series of `rw` tactics where
    // we should attempt to stack nodes with the same name together.
    // We will assume that nodes in the same layer are generated by
    // the same tactic.
    function hasCommonNodes(as: HypLayer[], b: HypLayer) {
      const lastLayer = as[as.length - 1];
      const prevIds = format.tactics.flatMap(t => t.hypArrows.flatMap(a => b.some(toNode => a.toId == toNode.id) && a.fromId ? a.fromId : []));
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
        const layerTactics = format.tactics.filter(t => t.hypArrows.some(a => layer.some(n => a.toId == n.id)));
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
          // TODO(lakesare): Improve to [fromId, toIds: [...]]
          const fromIds = new Set(tactic.hypArrows.map(a => a.fromId));
          for (const fromId of fromIds) {
            const nodes = layer.filter(n => tactic.hypArrows.some(a => a.fromId == fromId && a.toId == n.id));
            const tacticNode = createNode(
              parentId,
              tactic.text,
              "tactic",
              `${tactic.id}${fromId}${parentId}`,
            );
            if (fromId) {
              arrowsToDraw.push({ fromId, toShapeId: tacticNode.id });
            }
            arrowsToDraw.push(...nodes.map(n => ({ fromShapeId: tacticNode.id, toId: n.id })));
            // TODO: Have windows should be on the tactic not nodes.
            const haveWindows = format.windows
              .filter(w => nodes.some(n => n.haveWindowId == w.id))
              .map(w => createWindow(parentId, w, format));
            const hTree: HypTree = {
              tactic: vStack(0, hStack(inBetweenMargin, ...haveWindows), tacticNode), level, nodes: nodes.map(
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
            if (fromId) {
              nodeToTree.set(fromId, hTree)
            }
            topLevelTrees.add(hTree);
          }
        }
      }
      // Reverse because we were adding them bottom up but should prefer those which start earlier.
      rows.push(trees(inBetweenMargin, ...[...topLevelTrees.values()].reverse()));
    }
    const subWindows = format.windows.filter((w) => w.parentId == window.id);
    const frames: Element[] = [];
    for (const subWindow of subWindows) {
      frames.push(createWindow(parentId, subWindow, format));
    }
    if (frames.length > 0) {
      rows.push(hStack(inBetweenMargin, ...frames));
    }
    const goals: Element[] = [];
    for (const goalNode of [...window.goalNodes].reverse()) {
      const tactic = tactics.find(
        (t) =>
          t.goalArrows.some((a) => a.fromId == goalNode.id) ||
          t.successGoalId == goalNode.id
      );
      const tacticEls: Element[] = tactic
        ? [createNode(parentId,
          tactic.text + (tactic.successGoalId ? " 🎉" : ""),
          "tactic",
          tactic.id,
        )]
        : [];
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
      goals.push(vStack(0, ...tacticEls, goalEl));
    }
    rows.push(vStack(0, ...goals));
    return vStack(inBetweenMargin, ...rows);
  }

  const root = proofTree.windows.find((w) => w.parentId == null);
  if (root) {
    const el = createNodes(undefined, root, proofTree);
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

export default function Example(
  { proofTree, currentGoal }:
    { proofTree: Format | null, currentGoal: string | null }) {
  const [app, setApp] = useState<App | null>(null);
  if (app) {
    render(app, proofTree ?? { windows: [], tactics: [] }, currentGoal ?? '');
  }
  const handleMount = (app: App) => {
    setTimeout(() => {
      app.zoomToFit({ duration: 100 });
    }, 200);
    addEventListener("resize", (event) => {
      app.zoomToFit({ duration: 100 });
    });
    setApp(app);
  };
  return (
    <div
      style={{
        position: "fixed",
        inset: 0,
      }}
    >
      <Tldraw onMount={handleMount} config={config}></Tldraw>
    </div>
  );
}

let lastId = 0;

function Main() {
  const [proofTree, setProofTree] = useState<Format | null>(null);
  const [currentGoal, setCurrentGoal] = useState<string | null>(null);
  useEffect(() => {
    function getTypes() {
      fetch("getTypes")
        .then((response) => response.json())
        .then((res) => {
          const proofTree = res.data;
          const id = Number(res.id);
          if (id > lastId) {
            if (proofTree.steps.length > 0) {
              console.log(id, proofTree);
              const edges = toEdges(proofTree.steps);
              // TODO: Add ids to tactics as we will need that. Make it at converter
              edges.tactics = edges.tactics.map((t: any, idx: number) => ({ ...t, id: `tactic${idx}` }));
              console.log("Converted", edges);
              setProofTree(edges);
              setCurrentGoal(proofTree.goal);
            } else {
              console.log("Empty proof");
            }
            lastId = id;
          }
        })
        .catch((e) => {
          console.log("error", e);
        });
    }
    const interval = setInterval(getTypes, 200);
    return () => clearInterval(interval);
  }, []);
  return <Example proofTree={proofTree} currentGoal={currentGoal} />;
}

ReactDOM.render(
  <React.StrictMode>
    <Main />
  </React.StrictMode>,
  document.getElementById("root")
);
