import * as React from "react";
import { useState } from "react";
import { useEffect } from "react";
import * as ReactDOM from "react-dom";
import {
  App,
  LABEL_FONT_SIZES,
  TEXT_PROPS,
  TLParentId,
  Tldraw,
  TldrawEditorConfig,
  toolbarItem,
} from "@tldraw/tldraw";
import "@tldraw/tldraw/editor.css";
import "@tldraw/tldraw/ui.css";
import { toEdges } from "./converter";
import { WindowShape } from "./window";

interface Element {
  size: [number, number];
  draw: (x: number, y: number) => void;
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

function hStack(margin: number, ...boxes: Element[]): Element {
  if (boxes.length == 0) return { size: [0, 0], draw: () => { } };
  return {
    size: [
      boxes.map((b) => b.size[0]).reduce((x, y) => x + y) + (boxes.length - 1) * margin,
      Math.max(...boxes.map((b) => b.size[1])),
    ],
    draw(x, y) {
      let dx = 0;
      for (const box of boxes) {
        box.draw(x + dx, y);
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

function grid(vMargin: number, hMargin: number, ...rows: Element[][]): Element {
  if (rows.length == 0) return { size: [0, 0], draw: () => { } };
  const rowSizes = rows.map((row) => hStack(hMargin, ...row).size);
  const colSizes = transpose(rows).map((col) => vStack(vMargin, ...col).size);
  return {
    size: [
      colSizes.map((s) => s[0]).reduce((x, y) => x + y) + (colSizes.length - 1) * hMargin,
      rowSizes.map((s) => s[1]).reduce((x, y) => x + y) + (rowSizes.length - 1) * vMargin,
    ],
    draw(x0, y) {
      for (let i = 0; i < rows.length; i++) {
        let x = x0;
        for (let j = 0; j < rows[i].length; j++) {
          rows[i][j].draw(x, y);
          x += colSizes[j][0] + hMargin;
        }
        y += rowSizes[i][1] + vMargin;
      }
    }
  }
}

type Node = { text: string; id: string; name?: string; subNodes?: NodeLayer[] };
type Tactic = {
  text: string;
  fromNodeIds: string[];
  dependsOnIds: string[];
  toNodeIds: string[];
};

type NodeLayer = Node[];

interface GoalNode {
  text: string;
  id: string;
}

interface HypNode {
  text: string;
  name: string;
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

interface NewTactic {
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
  tactics: NewTactic[];
}

const config = new TldrawEditorConfig({
  shapes: [WindowShape],
  allowUnknownShapes: true,
});

function render(app: App, proofTree: Format) {
  app.updateInstanceState({ isFocusMode: true });

  const inBetweenMargin = 20;
  const framePadding = 20;

  const { tactics } = proofTree;

  const createNode = (
    parentId: TLParentId | undefined,
    text: string,
    type: "value" | "tactic" | "redvalue" = "value"
  ): Element => {
    const [w, h] = getTextSize(text);
    return {
      size: [w, h],
      draw(x, y) {
        app.createShapes([
          {
            id: app.createShapeId(),
            type: "geo",
            x,
            y,
            parentId,
            props: {
              geo: "rectangle",
              w,
              h,
              ...(type == "value"
                ? { dash: "draw", fill: "solid", color: "light-green" }
                : type == "redvalue"
                  ? { dash: "draw", fill: "solid", color: "light-red" }
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
      fontFamily: "draw",
      fontSize: LABEL_FONT_SIZES["m"],
      width: "fit-content",
      padding: "16px",
    });
    return [
      // Don't know how to calculate size correctly yet
      size.w * 1.3,
      size.h,
    ];
  }

  app.selectAll().deleteShapes();

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
      return lastLayer.some((n) => b.some((m) => n.name == m.name));
    }
    const rwSeqs: HypLayer[][] = [];
    for (const layer of window.hypNodes) {
      if (rwSeqs.length > 0 && hasCommonNodes(rwSeqs[rwSeqs.length - 1], layer)) {
        rwSeqs[rwSeqs.length - 1].push(layer);
      } else {
        rwSeqs.push([layer]);
      }
    }
    for (const rwSeq of rwSeqs) {
      const colNames: string[] = [];
      for (const layer of rwSeq) {
        for (const node of layer) {
          if (!colNames.includes(node.name)) {
            colNames.push(node.name);
          }
        }
      }

      const g: Element[][] = []
      for (const colName of colNames) {
        const col: Element[] = [];
        for (const layer of rwSeq) {
          const node = layer.find((n) => n.name == colName);
          if (node) {
            const tactic = format.tactics.find((t) =>
              t.hypArrows.some((a) => a.toId == node.id)
            );
            const nodes: Element[] = [];
            const haveWindow = format.windows.find(
              (w) => node.haveWindowId && w.id == node.haveWindowId
            );
            if (haveWindow) {
              nodes.push(createWindow(parentId, haveWindow, format));
            }
            if (tactic) {
              nodes.push(createNode(
                parentId,
                tactic.text,
                "tactic"
              ));
            }
            // For cases h._@.Examples._hyg.1162
            const hypName = node.name.includes(".")
              ? `${node.name.split(".")[0]}✝`
              : node.name;
            nodes.push(createNode(parentId, `${hypName}: ${node.text}`));
            col.push(vStack(0, ...nodes));
          } else {
            col.push(emptyEl());
          }
        }
        g.push(col);
      }
      rows.push(grid(0, inBetweenMargin, ...transpose(g)));
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
    const proved = tactics.some(
      (t) => t.successGoalId == window.goalNodes[0].id
    );
    for (const goalNode of [...window.goalNodes].reverse()) {
      const tactic = tactics.find(
        (t) =>
          t.goalArrows.some((a) => a.fromId == goalNode.id) ||
          t.successGoalId == goalNode.id
      );
      const tacticEls: Element[] = tactic
        ? [createNode(parentId, tactic.text, "tactic")]
        : [];
      const goalEl: Element = createNode(
        parentId,
        goalNode.text,
        proved ? "value" : "redvalue"
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
}

export default function Example({ proofTree }: { proofTree: Format | null }) {
  console.log("Example called");
  const [app, setApp] = useState<App | null>(null);
  if (app) {
    render(app, proofTree ?? { windows: [], tactics: [] });
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
              console.log("Converted", edges);
              setProofTree(edges);
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
  return <Example proofTree={proofTree} />;
}

ReactDOM.render(
  <React.StrictMode>
    <Main />
  </React.StrictMode>,
  document.getElementById("root")
);
