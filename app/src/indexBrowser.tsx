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

// Allowing certain properties on window
declare const window: PaperProofWindow;

function Main() {
  const [proofState, setProofState] = useState(window.initialInfo);
  const [proofTree, setProofTree] = useState<ConvertedProofTree | null>(null);
  const [highlights, setHighlights] = useState<Highlights | null>(null);
  const [perfectArrows, setPerfectArrows] = useState<Arrow[]>([]);

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
  
  React.useLayoutEffect(() => {
    if (!proofTree) return
    const newPerfectArrows = createArrows(proofTree);
    setPerfectArrows(newPerfectArrows);
  }, [proofTree]);

  return proofTree &&
  <div className="proof-tree">
    <ProofTree proofTree={proofTree} highlights={highlights}/>
    {perfectArrows.map((arrow, index) =>
      <PerfectArrow key={index} p1={arrow.from} p2={arrow.to}/>
    )}
  </div>
}

const root = createRoot(document.getElementById("root")!);
root.render(<Main/>);
