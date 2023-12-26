import React, { useEffect, useState } from "react";
import { createRoot } from 'react-dom/client';
import { ProofResponse, PaperProofWindow, ConvertedProofTree, Highlights, Arrow, ValidProofResponse } from "types";
import "./index.css";
import ProofTree from "./components/ProofTree";
import converter from "./services/converter";
import getHighlights from "./components/ProofTree/services/getHighlights";
import hypsToTables from "./services/hypsToTables";
import createArrows from './services/createArrows';
import PerfectArrow from "./components/PerfectArrow";

import Snackbar from '@mui/material/Snackbar';
import zoomOnNavigation from "./components/ProofTree/services/zoomOnNavigation";
import getStatement from "./services/getStatement";

// Allowing certain properties on window
declare const window: PaperProofWindow;

function Main() {
  const [proofTree, setProofTree] = useState<ConvertedProofTree | null>(null);
  const [highlights, setHighlights] = useState<Highlights | null>(null);
  const [perfectArrows, setPerfectArrows] = useState<Arrow[]>([]);
  const [lastValidProofResponse, setLastValidProofResponse] = useState<ValidProofResponse>(window.initialInfo);

  // We do need separate state vars for prettier animations
  const [snackbarMessage, setSnackbarMessage] = useState<String | null>(null);
  const [snackbarOpen, setSnackbarOpen] = useState<boolean>(false);


  useEffect(() => {
    addEventListener("message", (event) => {
      const proofResponse : ProofResponse = event.data as ProofResponse;

      // Does it ever happen?
      if (!proofResponse) {
        console.error("NO PROOOF???");
        return;
      };

      if ("error" in proofResponse) {
        if (proofResponse.error === 'File changed.' || proofResponse.error === 'stillTyping') {
          // This is a normal situation, just return.
        } else if (proofResponse.error === 'leanNotYetRunning') {
          setSnackbarMessage("Waiting for Lean");
          setSnackbarOpen(true);
        } else if (proofResponse.error.startsWith("No RPC method")) {
          setSnackbarMessage(`Missing "import Paperproof" in this file. Please import a Paperproof Lean library in this file.`);
          setSnackbarOpen(true);
        } else if (proofResponse.error === 'zeroProofSteps') {
          setSnackbarMessage("Not within theorem");
          setSnackbarOpen(true);
        } else {
          console.warn("We are not handling some error explicitly?", proofResponse);
        }
        return;
      }

      setSnackbarOpen(false);

      // ___Why don't we memoize these functions/avoid rerenders?
      //    These seem like expensive operations, however they aren't!
      //    The whole converter()+hypsToTables() process takes from 2ms to 5ms.
      //    The delay we see in the UI is coming from "Making getSnapshotData request" vscode rpc.
      const convertedProofTree : ConvertedProofTree = converter(proofResponse.proofTree);
      convertedProofTree.boxes.forEach((box) => {
        box.hypTables = hypsToTables(box.hypLayers, convertedProofTree)
      });
      setProofTree(convertedProofTree);

      const newHighlights = getHighlights(convertedProofTree.equivalentIds, proofResponse.goal);
      setHighlights(newHighlights);

      // Delete stored zoomedBoxId if we switched the theorems.
      const currentStatement = getStatement(proofResponse.proofTree);
      const lastStatement = getStatement(lastValidProofResponse.proofTree);
      if (lastStatement !== currentStatement) {
        localStorage.removeItem('zoomedBoxId');
      }
      setLastValidProofResponse(proofResponse);
    });
  }, [])

  React.useLayoutEffect(() => {
    if (!proofTree) return;
    const newPerfectArrows = createArrows(proofTree);
    setPerfectArrows(newPerfectArrows);
  
    zoomOnNavigation(proofTree, lastValidProofResponse.goal?.mvarId);
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
