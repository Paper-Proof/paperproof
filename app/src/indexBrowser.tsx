import * as React from "react";
import { useState } from "react";
import * as ReactDOM from "react-dom";
import { Editor as App, Tldraw } from "@tldraw/tldraw";
import { ProofState } from "./types";
import { buildProofTree } from "./buildProofTree";
import WindowUtil from "./shapes/WindowUtil";
import { createClient } from "@supabase/supabase-js";
import focusProofTree from './focusProofTree';

import '@tldraw/tldraw/tldraw.css'
import "./index.css";

const customShapeUtils = [WindowUtil];

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

function Main() {
  const [proofState, setProofState] = useState<ProofState | null>(null);
  const [app, setApp] = useState<App | null>(null);

  function updateUi(app: App, newProofState: ProofState | { error: any }) {
    console.log({ newProofState, proofState });

    if ("error" in newProofState) {
      app.selectAll().deleteShapes();
      console.log("setting proof state to", null);
      setProofState(null);
      return;
    }

    if (!areObjectsEqual(newProofState.proofTree, proofState?.proofTree ?? {})) {
      buildProofTree(app, newProofState.proofTree, uiConfig);
    }

    if (!areObjectsEqual(newProofState.goal, proofState?.goal ?? {})) {
      focusProofTree(
        app,
        newProofState.proofTree.equivalentIds,
        newProofState.goal
      );
    }

    console.log("setting proof state to", newProofState);
    setProofState(newProofState);
  }

  const handleMount = (app: App) => {
    console.log("handling mount");

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
          console.log("Updating UI because: supabase.from('sessions')");
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
            const newProofState = (payload.new as any)["proof"];
            console.log("Updating UI because: supabase.channel('proof-update')");
            updateUi(app, newProofState);
          }
        )
        .subscribe();
    }
    if (window.initialInfo) {
      console.log("Updating UI because: window.intialInfo");
      updateUi(app, window.initialInfo);
    }

    // Listen for direct messages from extension instead of round trip through server
    addEventListener("message", (event) => {
      console.log("Updating UI because: 'message' from extension");
      updateUi(app, event.data);
    });

    setApp(app);
  };

  return (
    <div className="tldraw-wrapper">
      <Tldraw
        onMount={handleMount}
        shapeUtils={customShapeUtils}
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
