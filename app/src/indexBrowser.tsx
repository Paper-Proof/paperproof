import * as React from "react";
import { useRef } from "react";
import { createRoot } from 'react-dom/client';
import { createClient } from "@supabase/supabase-js";
import { Editor, Tldraw } from "@tldraw/tldraw";

import WindowUtil from "./shapes/WindowUtil";
import CustomArrowUtil from "./shapes/CustomArrowUtil";
import CustomNodeUtil from "./shapes/CustomNodeUtil";
import updateUI from "./services/updateUI";
import clearTldrawCache from "./services/clearTldrawCache";

import { ProofResponse, PaperProofWindow } from "./types";

import '@tldraw/tldraw/tldraw.css'
import "./index.css";

// Tldraw saves too much, might create bugs/make development confusing in some cases
clearTldrawCache();

const customShapeUtils = [WindowUtil, CustomArrowUtil, CustomNodeUtil];

const supabaseUrl = "https://rksnswkaoajpdomeblni.supabase.co";
const supabaseKey =
  "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJpc3MiOiJzdXBhYmFzZSIsInJlZiI6InJrc25zd2thb2FqcGRvbWVibG5pIiwicm9sZSI6ImFub24iLCJpYXQiOjE2OTAwNjU2NjgsImV4cCI6MjAwNTY0MTY2OH0.gmF1yF-iBhzlUgalz1vT28Jbc-QoOr5OlgI2MQ5OXhg";
const supabase = createClient(supabaseUrl, supabaseKey);

declare const window: PaperProofWindow;

function Main() {
  const oldProofRef = useRef<ProofResponse>(null);

  const handleMount = (editor: Editor) => {
    editor.updateInstanceState({ isFocusMode: true });
    editor.user.updateUserPreferences({ isSnapMode: true });

    editor.renderingBoundsMargin = Infinity;

    if (window.sessionId) {
      console.log("Handling mount: browser mode");

      // 1. Render initial proof
      supabase.from("sessions").select("*").eq("id", window.sessionId).then((response) => {
        if (response.error) {
          console.error("Error fetching initial state", response.error);
          return;
        }
        const proof = response.data[0].proof;
        updateUI(editor, oldProofRef.current, proof)
        oldProofRef.current = proof;
      });

      // 2. Render the proof on updates
      supabase.channel("proof-update").on(
        "postgres_changes",
        {
          event: "*",
          schema: "public",
          table: "sessions",
          filter: `id=eq.${window.sessionId}`,
        },
        (payload) => {
          const proof = (payload.new as any)["proof"];
          updateUI(editor, oldProofRef.current, proof)
          oldProofRef.current = proof;
        }
      )
      .subscribe();
    } else if (window.initialInfo) {
      console.log("Handling mount: extension mode");

      // 1. Render initial proof
      const proof = window.initialInfo;
      updateUI(editor, oldProofRef.current, proof)
      oldProofRef.current = proof;

      // 2. Render the proof on updates
      addEventListener("message", (event) => {
        const proof = event.data;
        updateUI(editor, oldProofRef.current, proof)
        oldProofRef.current = proof;
      });
    }
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

const root = createRoot(document.getElementById("root")!);
root.render(
  <React.StrictMode>
    <Main/>
  </React.StrictMode>
);
