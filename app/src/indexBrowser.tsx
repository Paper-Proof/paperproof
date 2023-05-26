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

  type Size = [number, number];
  const { tactics } = proofTree;

  function vStack(margin: number, ...boxes: Size[]): Size {
    if (boxes.length == 0) return [0, 0];
    const w = Math.max(...boxes.map((b) => b[0]));
    const h = boxes.map((b) => b[1]).reduce((x, y) => x + y);
    return [w, h + (boxes.length - 1) * margin];
  }

  function hStack(margin: number, ...boxes: Size[]): Size {
    if (boxes.length == 0) return [0, 0];
    const w = boxes.map((b) => b[0]).reduce((x, y) => x + y);
    const h = Math.max(...boxes.map((b) => b[1]));
    return [w + (boxes.length - 1) * margin, h];
  }

  const drawNode = (
    parentId: TLParentId | undefined,
    text: string,
    [x, y]: [number, number],
    type: "value" | "tactic" | "redvalue" = "value"
  ): Size => {
    const [w, h] = getSize({ text, id: "aa" });
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
    return [w, h];
  };

  function getTreeSize(layers: NodeLayer[]): [number, number] {
    return vStack(
      inBetweenMargin,
      ...layers.map((l) => hStack(inBetweenMargin, ...l.map(getSize)))
    );
  }

  function getFrameSize(layers: NodeLayer[]): [number, number] {
    const size = getTreeSize(layers);
    return [size[0] + framePadding * 2, size[1] + framePadding * 2];
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

  function getSize(node: Node): [number, number] {
    const sizes: Size[] = [];
    sizes.push(getTextSize(node.text));
    const frameSize: Size = node.subNodes
      ? getFrameSize(node.subNodes)
      : [0, 0];
    return vStack(0, frameSize, ...sizes);
  }
  app.selectAll().deleteShapes();

  function getTactics(
    node: Node,
    tactics: Tactic[]
  ): [Tactic | undefined, Tactic | undefined] {
    const toValueTactic = tactics.find(
      (t) => t.toNodeIds.length == 1 && t.toNodeIds.includes(node.id)
    );
    const fromValueTactic = tactics.find(
      (t) => t.fromNodeIds.length == 1 && t.fromNodeIds.includes(node.id)
    );
    return [toValueTactic, fromValueTactic];
  }

  function drawNodes(
    parentId: TLParentId | undefined,
    window: Window,
    format: Format
  ): Size {
    let rows: Size[] = [];
    let y = framePadding;
    for (const layer of window.hypNodes) {
      const sizes: Size[] = [];
      let x = framePadding;
      for (const node of layer) {
        const tactic = format.tactics.find((t) =>
          t.hypArrows.some((a) => a.toId == node.id)
        );
        const nodes: Size[] = [];
        const haveWindow = format.windows.find(
          (w) => node.haveWindowId && w.id == node.haveWindowId
        );
        if (haveWindow) {
          const frameId = app.createShapeId();
          app.createShapes([
            {
              id: frameId,
              type: "window",
              x,
              y: y + vStack(0, ...nodes)[1],
              parentId,
              props: { name: haveWindow.id },
            },
          ]);
          const [w, h] = drawNodes(frameId, haveWindow, format);
          nodes.push([w, h]);
          app.updateShapes([{ id: frameId, type: "window", props: { w, h } }]);
        }
        if (tactic) {
          const sz = drawNode(
            parentId,
            tactic.text,
            [x, y + vStack(0, ...nodes)[1]],
            "tactic"
          );
          nodes.push(sz);
        }
        // For cases h._@.Examples._hyg.1162
        const hypName = node.name.includes(".")
          ? `${node.name.split(".")[0]}✝`
          : node.name;
        const hypSize: Size = drawNode(parentId, `${hypName}: ${node.text}`, [
          x,
          y + vStack(0, ...nodes)[1],
        ]);
        nodes.push(hypSize);
        const size = vStack(0, ...nodes);
        sizes.push(size);
        x += size[0] + inBetweenMargin;
      }
      rows.push(hStack(inBetweenMargin, ...sizes));
      y += hStack(0, ...sizes)[1] + inBetweenMargin;
    }
    const subWindows = format.windows.filter((w) => w.parentId == window.id);
    let x = framePadding;
    const frameSizes: Size[] = [];
    for (const subWindow of subWindows) {
      const frameId = app.createShapeId();
      app.createShapes([
        {
          id: frameId,
          type: "window",
          x,
          y,
          parentId,
          props: { name: subWindow.goalNodes[0].text },
        },
      ]);
      const [w, h] = drawNodes(frameId, subWindow, format);
      frameSizes.push([w, h]);
      app.updateShapes([{ id: frameId, type: "window", props: { w, h } }]);
      x += w + inBetweenMargin;
    }
    if (frameSizes.length > 0) {
      const frames = hStack(inBetweenMargin, ...frameSizes);
      rows.push(frames);
      y += frames[1] + inBetweenMargin;
    }
    const goals: Size[] = [];
    const proved = tactics.some(
      (t) => t.successGoalId == window.goalNodes[0].id
    );
    for (const goalNode of [...window.goalNodes].reverse()) {
      const tactic = tactics.find(
        (t) =>
          t.goalArrows.some((a) => a.fromId == goalNode.id) ||
          t.successGoalId == goalNode.id
      );
      const tacticSize: Size[] = tactic
        ? [drawNode(parentId, tactic.text, [framePadding, y], "tactic")]
        : [];
      const goalSize: Size = drawNode(
        parentId,
        goalNode.text,
        [framePadding, y + vStack(0, ...tacticSize)[1]],
        proved ? "value" : "redvalue"
      );
      const size = vStack(0, ...tacticSize, goalSize);
      goals.push(size);
      y += size[1];
    }
    rows.push(vStack(0, ...goals));
    const size = vStack(inBetweenMargin, ...rows);
    return [size[0] + 2 * framePadding, size[1] + 2 * framePadding];
  }

  const root = proofTree.windows.find((w) => w.parentId == null);
  if (root) {
    drawNodes(undefined, root, proofTree);
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
