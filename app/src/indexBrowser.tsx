import * as React from "react";
import { useState } from "react";
import * as ReactDOM from "react-dom";
import { Editor as App, Tldraw } from "@tldraw/tldraw";
import { Format, InteractiveGoal, ProofState } from "./types";
import { buildProofTree } from "./buildProofTree";
import { WindowShape } from "./shapes/WindowShape";
import WindowUtil from "./shapes/WindowUtil";
import { createNodeId } from "./buildProofTree/services/CreateId";
import { createClient } from "@supabase/supabase-js";

import '@tldraw/tldraw/tldraw.css'
import "./index.css";

const supabaseUrl = "https://rksnswkaoajpdomeblni.supabase.co";
const supabaseKey =
  "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJpc3MiOiJzdXBhYmFzZSIsInJlZiI6InJrc25zd2thb2FqcGRvbWVibG5pIiwicm9sZSI6ImFub24iLCJpYXQiOjE2OTAwNjU2NjgsImV4cCI6MjAwNTY0MTY2OH0.gmF1yF-iBhzlUgalz1vT28Jbc-QoOr5OlgI2MQ5OXhg";
const supabase = createClient(supabaseUrl, supabaseKey);

interface PaperProofWindow extends Window {
  sessionId: string | null;
  initialInfo: any | null;
}

declare const window: PaperProofWindow;

// TODO: We should use the vscode font for consistency with Lean probably
// const fontFamily = 'Menlo, Monaco, "Courier New", monospace;'

const uiConfig = {
  // Ideally it should be `hideNonContributingHyps` to hide all hyps which aren't contributing
  // to goals in any way, but determining what hyps are used in what tactics isn't implemented
  // properly yet, e.g. in linarith.
  hideNulls: true,
};

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
    const existingNodes = app.shapesArray
      .filter((shape) => shape.id.startsWith("shape:node-"))
      .map((node) => ({
        id: node.id,
        type: "geo",
        // props: {
        //   opacity: "1",
        // },
      }));
    app.updateShapes(existingNodes);
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
  const focusedShapes = app.shapesArray
    .filter((shape) => shape.id.startsWith("shape:node-"))
    .map((node) => {
      const ifFocused =
        node.id === focusedGoalId || focusedHypIds.includes(node.id);
      return {
        id: node.id,
        type: "geo",
        // TODO:update opacity doesn't work
        // props: {
        //   opacity: ifFocused ? "1" : "0.25",
        // },
      };
    });
  app.updateShapes(focusedShapes);
};

function Main() {
  const [proofState, setProofState] = useState<ProofState | null>(null);
  const [app, setApp] = useState<App | null>(null);

  function updateUi(app: App, newProofState: ProofState | { error: any }) {
    console.log({ newProofState, proofState });

    if ("error" in newProofState) {
      app.selectAll().deleteShapes();
      // setProofState(null);
      return;
    }

    if (
      !areObjectsEqual(newProofState.proofTree, proofState?.proofTree ?? {})
    ) {
      buildProofTree(app, newProofState.proofTree, uiConfig);
    }

    if (!areObjectsEqual(newProofState.goal, proofState?.goal ?? {})) {
      focusProofTree(
        app,
        newProofState.proofTree.equivalentIds,
        newProofState.goal
      );
    }

    // setProofState(newProofState);
  }

  const handleMount = (app: App) => {
    console.log("handling mount");
    setTimeout(() => {
      app.zoomToFit({ duration: 100 });
    }, 200);

    if (window.sessionId) {
      // This is loaded in browser.
      console.log("Browser mode");

      // Get initial state
      supabase
        .from("sessions")
        .select("*")
        .eq("id", window.sessionId)
        .then((res) => {
          if (res.error) {
            console.error("Error fetching initial state", res.error);
            return;
          }
          const proof = res.data[0].proof;
          updateUi(app, proof);
        });

      // Listen for changes
      supabase
        .channel("proof-update")
        .on(
          "postgres_changes",
          {
            event: "*",
            schema: "public",
            table: "sessions",
            filter: `id=eq.${window.sessionId}`,
          },
          (payload) => {
            console.log("Got response from supabase", payload);
            const newProofState = (payload.new as any)["proof"];
            updateUi(app, newProofState);
          }
        )
        .subscribe();
    }
    if (window.initialInfo) {
      updateUi(app, window.initialInfo);
    }

    // Listen for direct messages from extension instead of round trip through server
    addEventListener("message", (event) => {
      updateUi(app, event.data);
    });

    // addEventListener("resize", (event) => {
    //   app.zoomToFit({ duration: 100 });
    // });
    // TODO:update
    // app.userDocumentSettings.isSnapMode = true;
    // app.updateInstanceState({ isFocusMode: true });

    // TODO:update the new tldraw version errors out with cryptic errors when we `setAnyState()` in `onMount()`.
    // This doesn't happen in tldraw's main branch.
    // setApp(app);
  };

  return (
    <div className="tldraw-wrapper">
      <Tldraw
        onMount={handleMount}
        shapeUtils={[WindowUtil]}
        // TODO:update cant find this option in the new tldraw version, return if it's still needed
        // allowUnknownShapes: true,
      />
    </div>
  );
}

ReactDOM.render(
  <React.StrictMode>
    <Main />
  </React.StrictMode>,
  document.getElementById("root")
);
