import React, { useEffect, useState } from "react";
import { useRef } from "react";
import { createRoot } from 'react-dom/client';
import { Canvas, ContextMenu, Editor, Tldraw } from "@tldraw/tldraw";

import WindowUtil      from "./tldraw/shapes/WindowUtil";
import CustomArrowUtil from "./tldraw/shapes/CustomArrowUtil";
import CustomNodeUtil  from "./tldraw/shapes/CustomNodeUtil";

import ErrorToast from "./tldraw/components/ErrorToast";

import updateUI from "./services/updateUI";
import clearTldrawCache from "./services/clearTldrawCache";

import { ProofResponse, PaperProofWindow } from "types";

import '@tldraw/tldraw/tldraw.css'
import "./index.css";
import uiOverrides from "./tldraw/uiOverrides";
import { Simple } from "./simple";
import { New } from "./new/New";

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
  const [proofState, setProofState] = useState(window.initialInfo);

  useEffect(() => {
    addEventListener("message", (event) => {
      const proof = event.data;
      setProofState(proof);
    });
  }, [])

  return <New proofState={proofState}/>
  // return <Simple/>
}

const root = createRoot(document.getElementById("root")!);
root.render(
  // We get a double component mount with StrictMode
  // (https://stackoverflow.com/a/64394524/3192470)
  // <React.StrictMode>
    <Main/>
  // </React.StrictMode>
);
