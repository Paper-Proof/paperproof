import * as React from "react";
import { useState } from "react";
import * as ReactDOM from "react-dom";
import "@tldraw/tldraw/editor.css";
import "@tldraw/tldraw/ui.css";
import "./index.css";
import { Format, InteractiveHyp, InteractiveGoal, ApiResponse } from "./types";
import { buildProofTree } from './buildProofTree';
import { WindowShape } from "./shapes/WindowShape";
import { CustomArrowShape } from "./shapes/CustomArrowShape";
import { createNodeId } from './buildProofTree/services/CreateId'

import { useInterval } from 'usehooks-ts'

import {
  App,
  Tldraw,
  TldrawEditorConfig,
  TLShapeId
} from "@tldraw/tldraw";

const BASE_URL = "http://localhost:80";

// TODO: We should use the vscode font for consistency with Lean probably
// const fontFamily = 'Menlo, Monaco, "Courier New", monospace;'

const uiConfig = {
  // Ideally it should be `hideNonContributingHyps` to hide all hyps which aren't contributing
  // to goals in any way, but determining what hyps are used in what tactics isn't implemented
  // properly yet, e.g. in linarith.
  hideNulls: true,
};

const config = new TldrawEditorConfig({
  shapes: [WindowShape, CustomArrowShape],
  allowUnknownShapes: true,
});

const areObjectsEqual = (a: object, b: object) => {
  return JSON.stringify(a) === JSON.stringify(b);
};

// This could be done in /extension, but doing it here for the ease of debugging
const getDisplayedId = (equivalentIds: Format["equivalentIds"], id: string) => {
  const displayedId = Object.keys(equivalentIds).find((displayedId) =>
    equivalentIds[displayedId].find((inferiorId) => inferiorId === id)
  );
  return displayedId ? displayedId : id;
};

const focusProofTree = (
  app: App,
  equivalentIds: Format["equivalentIds"],
  currentGoal: InteractiveGoal | null
) => {
  if (currentGoal === null) {
    const existingNodeIds = Array.from(app.shapeIds.values())
      .filter((shapeId) => shapeId.startsWith("shape:node-"))
      .map((nodeId) => ({
        id: nodeId,
        type: "geo",
        props: {
          opacity: "1",
        },
      }));
    app.updateShapes(existingNodeIds);
    return;
  }

  const focusedGoalId = createNodeId(
    app,
    getDisplayedId(equivalentIds, currentGoal.mvarId)
  );
  const focusedHypIds = currentGoal.hyps
    .reduce<string[]>((acc, hyp) => [...acc, ...hyp.fvarIds], [])
    .map((inferiorHypId) => {
      const hypId = getDisplayedId(equivalentIds, inferiorHypId);
      return createNodeId(app, hypId);
    });
  const focusedShapes = Array.from(app.shapeIds.values())
    .filter((shapeId) => shapeId.startsWith("shape:node-"))
    .map((nodeId) => {
      const ifFocused =
        nodeId === focusedGoalId || focusedHypIds.includes(nodeId);
      return {
        id: nodeId,
        type: "geo",
        props: {
          opacity: ifFocused ? "1" : "0.25",
        },
      };
    });
  app.updateShapes(focusedShapes);
};

const updateUi = (
  app: App,
  newResponse: ApiResponse,
  oldResponse: ApiResponse | null
) => {
  console.log({ newResponse, oldResponse });

  if (!areObjectsEqual(newResponse.proofTree, oldResponse?.proofTree ?? {})) {
    buildProofTree(app, newResponse.proofTree, uiConfig);
  }

  if (!areObjectsEqual(newResponse.goal, oldResponse?.goal ?? {})) {
    focusProofTree(app, newResponse.proofTree.equivalentIds, newResponse.goal);
  }
};

function Main() {
  const [apiResponse, setApiResponse] = useState<ApiResponse | null>(null);
  const [app, setApp] = useState<App | null>(null);
  const [sessionId, setSessionId] = useState<string | null>(null);

  const BY_POST_MESSAGE = "by post message";

  useInterval(() => {
    if (apiResponse && apiResponse.id == BY_POST_MESSAGE) {
      // It runs as an extension and communicates changes directly
      return;
    }
    fetch(`${BASE_URL}/getTypes`)
      .then((response) => response.json())
      .then((newResponse) => {
        if (
          apiResponse &&
          (apiResponse.id === BY_POST_MESSAGE ||
            newResponse.id === apiResponse.id)
        )
          return;
        if (!app) return;

        // TODO: Errors from both server and extension should be handled uniformly
        // in one place.
        // TODO insert this into extension too when code is more stable
        // @ts-ignore
        if (!newResponse.proofTree || newResponse.error) {
          app.selectAll().deleteShapes();
          setApiResponse(null);
          return;
        }

        updateUi(app, newResponse, apiResponse);

        setApiResponse(newResponse);
      })
      .catch((e) => {
        console.error("server error", e);
      });
  }, 200);
  const handleMount = (app: App) => {
    setTimeout(() => {
      app.zoomToFit({ duration: 100 });
    }, 200);

    // Listen for direct messages from extension instead of round trip through server
    addEventListener("message", (event) => {
      if (event.data["sessionId"]) {
        setSessionId(event.data["sessionId"]);
      }
      if (!app || !event.data["proofTree"]) return;
      const newResponse: ApiResponse = { ...event.data, id: BY_POST_MESSAGE };

      updateUi(app, newResponse, apiResponse);

      setApiResponse(newResponse);
    });

    addEventListener("resize", (event) => {
      app.zoomToFit({ duration: 100 });
    });
    app.userDocumentSettings.isSnapMode = true;
    app.updateInstanceState({ isFocusMode: true });
    setApp(app);
  };

  const baseUrl = "https://unpkg.com/@tldraw/assets@2.0.0-alpha.14/";
  return (
    <div className="tldraw-wrapper">
      <Tldraw
        onMount={handleMount}
        config={config}
        baseUrl={baseUrl}
        assetBaseUrl={baseUrl}
      />
    </div>
  );
}

ReactDOM.render(
  <React.StrictMode>
    <Main/>
  </React.StrictMode>,
  document.getElementById("root")
);
