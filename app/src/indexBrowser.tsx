import React, { useEffect, useState } from "react";
import { createRoot } from 'react-dom/client';
import { ProofResponse, PaperProofWindow } from "types";
import "./index.css";
import { New } from "./new/New";

// Allowing certain properties on window
declare const window: PaperProofWindow;

function Main() {
  const [proofState, setProofState] = useState(window.initialInfo);

  useEffect(() => {
    addEventListener("message", (event) => {
      const proof = event.data;
      setProofState(proof);
    });
  }, [])

  return <New proofState={proofState}/>
}

const root = createRoot(document.getElementById("root")!);
root.render(
  // We get a double component mount with StrictMode
  // (https://stackoverflow.com/a/64394524/3192470)
  // <React.StrictMode>
    <Main/>
  // </React.StrictMode>
);
