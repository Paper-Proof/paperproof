import React, { useEffect, useState } from "react";
import { createRoot } from 'react-dom/client';
import { ProofResponse, PaperProofWindow } from "types";
import "./index.css";
import ProofTree from "./components/ProofTree";
// @ts-ignore
import LeaderLine from './services/LeaderLine.min.js';

// Allowing certain properties on window
declare const window: PaperProofWindow;

function Main() {
  const [proofState, setProofState] = useState(window.initialInfo);

  useEffect(() => {
    addEventListener("message", (event) => {
      const proof = event.data;
      setProofState(proof);
    });

    new LeaderLine(
      document.getElementById('hypothesis-_uniq.574'),
      document.getElementById('hypothesis-_uniq.730')
    );
  }, [])

  return <ProofTree proofState={proofState}/>
}

const root = createRoot(document.getElementById("root")!);
root.render(<Main/>);
