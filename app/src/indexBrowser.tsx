import React from "react";
import { useRef } from "react";
import { createRoot } from 'react-dom/client';
import { Canvas, ContextMenu, Editor, Tldraw } from "@tldraw/tldraw";

import WindowUtil      from "./shapes/WindowUtil";
import CustomArrowUtil from "./shapes/CustomArrowUtil";
import CustomNodeUtil  from "./shapes/CustomNodeUtil";

import ErrorToast from "./components/ErrorToast";

import updateUI from "./services/updateUI";
import clearTldrawCache from "./services/clearTldrawCache";

import { ProofResponse, PaperProofWindow } from "types";

import '@tldraw/tldraw/tldraw.css'
import "./index.css";

// Allowing certain properties on window
declare const window: PaperProofWindow;

// Tldraw saves too much, might create bugs/make development confusing in some cases
clearTldrawCache();

// These must be defined here, and not inline in a prop, or tldraw will error out in a cryptic way
const customShapeUtils = [WindowUtil, CustomArrowUtil, CustomNodeUtil];

const uiConfig = {
  // Ideally it should be `hideNonContributingHyps` to hide all hyps which aren't contributing to goals in any way, but determining what hyps are used in what tactics isn't implemented properly yet, e.g. in linarith.
  hideNulls: true,
};

function Main() {
  const oldProofRef = useRef<ProofResponse>(null);

  const handleMount = (editor: Editor) => {
    localStorage.removeItem('zoomedWindowId');

    editor.updateInstanceState({ isFocusMode: true });
    editor.user.updateUserPreferences({ isSnapMode: true });
    editor.renderingBoundsMargin = Infinity;

    // 1. Render initial proof
    const proof = window.initialInfo;
    updateUI(editor, oldProofRef.current, proof, uiConfig)
    oldProofRef.current = proof;

    // 2. Render the proof on updates
    addEventListener("message", (event) => {
      const proof = event.data;
      updateUI(editor, oldProofRef.current, proof, uiConfig)
      oldProofRef.current = proof;
    });
  };

  return (
    <div className="tldraw-wrapper">
      <Tldraw onMount={handleMount} shapeUtils={customShapeUtils}>
        {/* ContextMeny is necessary for the right-click menu to appear */}
        <ContextMenu>
          <Canvas/>
          <ErrorToast/>
        </ContextMenu>
      </Tldraw>
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
