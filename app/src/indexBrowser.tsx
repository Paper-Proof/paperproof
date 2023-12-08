import React, { useEffect, useState } from "react";
import { createRoot } from 'react-dom/client';
import { ProofResponse, PaperProofWindow } from "types";
import "./index.css";
import ProofTree from "./components/ProofTree";
// @ts-ignore
import LeaderLine from './services/LeaderLine.min.js';
import createDependsOnArrows from './services/createDependsOnArrows';

// Allowing certain properties on window
declare const window: PaperProofWindow;

function Main() {
  const [proofState, setProofState] = useState(window.initialInfo);
  const [leaderLine, setLeaderLine] = useState<LeaderLine | null>(null);

  useEffect(() => {
    addEventListener("message", (event) => {
      const proof = event.data;
      setProofState(proof);
    });
  }, [])

  const refreshArrows = () => {    
    // Remove previous leaderLine if it exists
    if (leaderLine) {
      leaderLine.remove();
    }
    // Create new leaderLine and store it in state
    const newLeaderLine = createDependsOnArrows()
    setLeaderLine(newLeaderLine);
  }

  useEffect(() => {
    refreshArrows();
  }, [proofState]);

  return <ProofTree proofState={proofState}/>
}

const root = createRoot(document.getElementById("root")!);
root.render(<Main/>);
