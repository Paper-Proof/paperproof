import React, { useState } from "react";
import { createRoot } from "react-dom/client";
import { LatexSettings, Settings, SNAPSHOT_VERSION, SnapshotPayload } from "types";
import "@app/index.css";
import "@app/css/theorem.css";
import "./snapshotPage.css";
import hypsToTables from "@app/services/hypsToTables";

import ProofTreeView from "./components/ProofTreeView";
import ProofTreeErrorBoundary from "./components/ProofTreeErrorBoundary";

declare const window: Window & { PAPERPROOF_SNAPSHOT?: SnapshotPayload };

const SnapshotPage = ({ payload }: { payload: SnapshotPayload }) => {
  const [settings, setSettings] = useState<Settings>(payload.settings);
  const [collapsedBoxIds, setCollapsedBoxIds] = useState<string[]>(payload.collapsedBoxIds);
  const [deletedHypothesisNames, setDeletedHypothesisNames] = useState<string[]>(payload.deletedHypothesisNames);
  const [latexSettings, setLatexSettings] = useState<LatexSettings>(payload.latexSettings);

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

const payload = window.PAPERPROOF_SNAPSHOT;
const root = createRoot(document.getElementById("root")!);

if (!payload) {
  root.render(<div className="snapshot-message">This snapshot has no proof in it.</div>);
} else if (payload.version > SNAPSHOT_VERSION) {
  // [Claude comment] Only reachable via a stale cached bundle - better a message
  // than a mangled proof.
  root.render(
    <div className="snapshot-message">
      This snapshot was made by a newer version of Paperproof. Try a hard refresh.
    </div>
  );
} else {
  // [Claude comment] hypTables is a derived layout, so recompute it with today's
  // `hypsToTables` rather than trusting whatever shape the sender stored.
  payload.proofTree.boxes.forEach((box) => {
    box.hypTables = hypsToTables(box.hypLayers, payload.proofTree, payload.settings.isSingleTacticMode);
  });
  root.render(<SnapshotPage payload={payload}/>);
}
