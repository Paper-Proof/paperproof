import * as React from "react";
import { useState } from "react";
import { useEffect } from "react";
import * as ReactDOM from "react-dom";
import "@tldraw/tldraw/editor.css";
import "@tldraw/tldraw/ui.css";
import "./index.css";
import { toEdges } from "./converter";
import { Format } from "./types";
import { buildProofTree } from './buildProofTree';
import { WindowShape } from "./shapes/WindowShape";
import { CustomArrowShape } from "./shapes/CustomArrowShape";

import {
  App,
  Tldraw,
  TldrawEditorConfig,
} from "@tldraw/tldraw";

let lastId = 0;

// TODO: We should use the vscode font for consistency with Lean probably
// const fontFamily = 'Menlo, Monaco, "Courier New", monospace;'

const uiConfig = {
  // Ideally it should be `hideNonContributingHyps` to hide all hyps which aren't contributing
  // to goals in any way, but determining what hyps are used in what tactics isn't implemented
  // properly yet, e.g. in linarith.
  hideNulls: true,
}

const config = new TldrawEditorConfig({
  shapes: [WindowShape, CustomArrowShape],
  allowUnknownShapes: true
});

function Main() {
  const [proofTree, setProofTree] = useState<Format>({ windows: [], tactics: [] });
  const [currentGoal, setCurrentGoal] = useState<string>("");

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

  const [app, setApp] = useState<App | null>(null);

  if (app) {
    buildProofTree(app, proofTree, currentGoal, uiConfig);
  }

  const handleMount = (app: App) => {
    setTimeout(() => {
      app.zoomToFit({ duration: 100 });
    }, 200);
    addEventListener("resize", (event) => {
      app.zoomToFit({ duration: 100 });
    });
    app.userDocumentSettings.isSnapMode = true;
    app.updateInstanceState({ isFocusMode: true });
    setApp(app);
  };

  return (
    <div className="tldraw-wrapper">
      <Tldraw onMount={handleMount} config={config} />
    </div>
  );
}

ReactDOM.render(
  <React.StrictMode>
    <Main />
  </React.StrictMode>,
  document.getElementById("root")
);
