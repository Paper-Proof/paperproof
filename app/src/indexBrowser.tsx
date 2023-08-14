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

declare const window: PaperProofWindow;

function Main() {
  const oldProofRef = useRef<ProofResponse>(null);

  const handleMount = (editor: Editor) => {
    editor.updateInstanceState({ isFocusMode: true });
    editor.user.updateUserPreferences({ isSnapMode: true });
    editor.renderingBoundsMargin = Infinity;

    console.log("Handling Tldraw .onMount");

    // 1. Render initial proof
    console.log(`Rendering initial proof`);
    const proof = window.initialInfo;
    updateUI(editor, oldProofRef.current, proof)
    oldProofRef.current = proof;

    // 2. Render the proof on updates
    addEventListener("message", (event) => {
      console.log(`Rendering message`);
      const proof = event.data;
      updateUI(editor, oldProofRef.current, proof)
      oldProofRef.current = proof;
    });
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
  // We get a double component mount with StrictMode
  // (https://stackoverflow.com/a/64394524/3192470)
  // <React.StrictMode>
    <Main/>
  // </React.StrictMode>
);
