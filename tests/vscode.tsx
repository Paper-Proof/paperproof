import React, { useState } from "react";
import { createRoot } from "react-dom/client";
import { SnapshotPayload } from "types";
import "@app/index.css";
import "@app/css/theorem.css";
import hypsToTables from "@app/services/hypsToTables";
import ProofTreeView from "../embed/src/components/ProofTreeView";
import ProofTreeErrorBoundary from "../embed/src/components/ProofTreeErrorBoundary";

declare const window: Window & { PAPERPROOF_SNAPSHOT: SnapshotPayload };
const payload = window.PAPERPROOF_SNAPSHOT;
payload.proofTree.boxes.forEach((box) => {
  box.hypTables = hypsToTables(box.hypLayers, payload.proofTree, payload.settings.isSingleTacticMode);
});

const Page = () => {
  const [settings, setSettings] = useState(payload.settings);
  const [collapsedBoxIds, setCollapsedBoxIds] = useState(payload.collapsedBoxIds);
  const [deletedHypothesisNames, setDeletedHypothesisNames] = useState(payload.deletedHypothesisNames);
  const [latexSettings, setLatexSettings] = useState(payload.latexSettings);
  return (
    <ProofTreeErrorBoundary>
      <ProofTreeView
        proofTree={payload.proofTree}
        highlights={payload.highlights}
        settings={settings}                             setSettings={setSettings}
        collapsedBoxIds={collapsedBoxIds}               setCollapsedBoxIds={setCollapsedBoxIds}
        deletedHypothesisNames={deletedHypothesisNames} setDeletedHypothesisNames={setDeletedHypothesisNames}
        latexSettings={latexSettings}                   setLatexSettings={setLatexSettings}
      />
    </ProofTreeErrorBoundary>
  );
};

createRoot(document.getElementById("root")!).render(<Page/>);
