import React, { useEffect, useState } from "react";
import { createRoot } from 'react-dom/client';
import { ProofResponse, PaperProofWindow, ConvertedProofTree, Highlights } from "types";
import "./index.css";
import ProofTree from "./components/ProofTree";
import converter from "./services/converter";
import getHighlights from "./components/ProofTree/services/getHighlights";
import hypsToTables from "./services/hypsToTables";
// @ts-ignore
import LeaderLine from './services/LeaderLine.min.js';
import createArrows from './services/createArrows';

// Allowing certain properties on window
declare const window: PaperProofWindow;

function Main() {
  const [proofState, setProofState] = useState(window.initialInfo);
  const [proofTree, setProofTree] = useState<ConvertedProofTree | null>(null);
  const [highlights, setHighlights] = useState<Highlights | null>(null);
  const [leaderLines, setLeaderLines] = useState<LeaderLine[]>([]);

  useEffect(() => {
    addEventListener("message", (event) => {
      const proof = event.data;
      setProofState(proof);

      if (!proof || "error" in proof) {
        return;
      }

      const convertedProofTree : ConvertedProofTree = converter(proof.proofTree);
      convertedProofTree.boxes.forEach((box) => {
        box.hypTables = hypsToTables(box.hypLayers, convertedProofTree)
      });
      setProofTree(convertedProofTree);
      const newHighlights = getHighlights(convertedProofTree.equivalentIds, proof.goal);
      setHighlights(newHighlights);
    });
  }, [])
  
  useEffect(() => {
    if (proofTree) {
      leaderLines.forEach((leaderLine) => { leaderLine.remove(); });
      const newLeaderLines = createArrows(proofTree);
      setLeaderLines(newLeaderLines);
    }
  }, [proofTree])

  return proofTree && <ProofTree proofTree={proofTree} highlights={highlights}/>
}

const root = createRoot(document.getElementById("root")!);
root.render(<Main/>);
