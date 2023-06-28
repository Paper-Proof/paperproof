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
  LABEL_FONT_SIZES,
  TEXT_PROPS,
  TLParentId,
  TLShapeId,
  Tldraw,
  TldrawEditorConfig,
} from "@tldraw/tldraw";

let lastId = 0;

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
    buildProofTree(app, proofTree, currentGoal);
  }

  const handleMount = (app: App) => {
    setTimeout(() => {
      app.zoomToFit({ duration: 100 });
    }, 200);
    addEventListener("resize", (event) => {
      app.zoomToFit({ duration: 100 });
    });
    app.userDocumentSettings.isSnapMode = true;
    setApp(app);
  };

  return (
    <div style={{ position: "fixed", inset: 0 }}>
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
