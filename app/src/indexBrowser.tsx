import React, { useEffect, useState } from "react";
import { createRoot } from 'react-dom/client';
import { ProofResponse, PaperProofWindow, ConvertedProofTree, Highlights, Arrow } from "types";
import "./index.css";
import ProofTree from "./components/ProofTree";
import converter from "./services/converter";
import getHighlights from "./components/ProofTree/services/getHighlights";
import hypsToTables from "./services/hypsToTables";
import createArrows from './services/createArrows';
import PerfectArrow from "./components/PerfectArrow";

import Snackbar from '@mui/material/Snackbar';

// Allowing certain properties on window
declare const window: PaperProofWindow;

function Main() {
  const [proofState, setProofState] = useState<ProofResponse>(window.initialInfo);
  const [proofTree, setProofTree] = useState<ConvertedProofTree | null>(null);
  const [highlights, setHighlights] = useState<Highlights | null>(null);
  const [perfectArrows, setPerfectArrows] = useState<Arrow[]>([]);
  // We do need separate state vars for prettier animations
  const [snackbarMessage, setSnackbarMessage] = useState<String | null>(null);
  const [snackbarOpen, setSnackbarOpen] = useState<boolean>(false);

  useEffect(() => {
    addEventListener("message", (event) => {
      const proof = event.data;
      setProofState(proof);

      // Does it ever happen?
      if (!proof) return;

      if ("error" in proof) {
        if (proof.error === 'File changed.' || proof.error === 'stillTyping') {
          // This is a normal situation, just return.
        } else if (proof.error === 'leanNotYetRunning') {
          setSnackbarMessage("Waiting for Lean");
          setSnackbarOpen(true);
        } else if (proof.error.startsWith("No RPC method")) {
          setSnackbarMessage(`Missing "import Paperproof" in this file. Please import a Paperproof Lean library in this file.`);
          setSnackbarOpen(true);
        } else if (proof.error === 'zeroProofSteps') {
          setSnackbarMessage("Not within theorem");
          setSnackbarOpen(true);
        } else {
          console.warn("We are not handling some error explicitly?", proof);
        }
        return;
      }

      setSnackbarOpen(false);

      // ___Why don't we memoize these functions/avoid rerenders?
      //    These seem like expensive operations, however they aren't!
      //    The whole converter()+hypsToTables() process takes from 2ms to 5ms.
      //    The delay we see in the UI is coming from "Making getSnapshotData request" vscode rpc.
      const convertedProofTree : ConvertedProofTree = converter(proof.proofTree);
      convertedProofTree.boxes.forEach((box) => {
        box.hypTables = hypsToTables(box.hypLayers, convertedProofTree)
      });
      setProofTree(convertedProofTree);

      const newHighlights = getHighlights(convertedProofTree.equivalentIds, proof.goal);
      setHighlights(newHighlights);
    });
  }, [])
  
  React.useLayoutEffect(() => {
    if (!proofTree) return
    const newPerfectArrows = createArrows(proofTree);
    setPerfectArrows(newPerfectArrows);
  }, [proofTree]);

  return <>
    {
      proofTree &&
      <div className="proof-tree">
        <ProofTree proofTree={proofTree} highlights={highlights}/>
        {perfectArrows.map((arrow, index) =>
          <PerfectArrow key={index} p1={arrow.from} p2={arrow.to}/>
        )}
      </div>
    }
    <Snackbar
      open={snackbarOpen}
      autoHideDuration={null}
      message={snackbarMessage}
      anchorOrigin={{ vertical: 'bottom', horizontal: 'right' }}
    />
  </>
}

const root = createRoot(document.getElementById("root")!);
root.render(<Main/>);
