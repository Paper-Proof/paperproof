import React, { useState, useEffect } from "react";
import { createRoot } from 'react-dom/client';
import { ConvertedProofTree, LatexSettings, DEFAULT_LATEX_SETTINGS, NaturalProofTree, Arrow } from "types";
import "@app/index.css";
import "./naturalRenderer.css";
import "./proofPanel.css";
import hypsToTables from "@app/services/hypsToTables";
import naturalToConverted from "@app/services/naturalToConverted";
import createHypArrows from "@app/services/createHypArrows";
import PerfectArrow from "@app/components/PerfectArrow";
import JsonEditor from "./components/JsonEditor";
import { collectTexts } from "@app/services/convertToLatex";
import { llmInstructions, exampleJson } from "./services/llmInstructions";
import { StandaloneGlobalContext, useStandaloneGlobalContext } from "./proofContext";

import BoxEl from "@app/components/ProofTree/components/BoxEl";
import Nav from "./components/Nav";

const LS_KEY = 'paperproof-natural-json';

// Error boundary so a renderer crash never wipes the editor
class ProofTreeErrorBoundary extends React.Component<
  { children: React.ReactNode; onError: () => void },
  { hasError: boolean; message: string }
> {
  constructor(props: { children: React.ReactNode; onError: () => void }) {
    super(props);
    this.state = { hasError: false, message: '' };
  }
  static getDerivedStateFromError(error: Error) {
    return { hasError: true, message: error.message };
  }
  componentDidCatch() {
    this.props.onError();
  }
  render() {
    if (this.state.hasError) {
      return (
        <div className="natural-render-error">
          Renderer error: {this.state.message}
        </div>
      );
    }
    return this.props.children;
  }
}

const StandaloneProofTree = () => {
  const { proofTree } = useStandaloneGlobalContext();
  const rootBox = proofTree.boxes.find((box) => box.parentId === null);
  if (!rootBox) return null;
  return <BoxEl box={rootBox} />;
};

function StandaloneRenderer() {
  const [jsonInput, setJsonInput] = useState<string>(
    () => localStorage.getItem(LS_KEY) || ""
  );
  const [convertedProofTree, setConvertedProofTree] = useState<ConvertedProofTree | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [isEditing, setIsEditing] = useState<boolean>(false);
  const [renderKey, setRenderKey] = useState<number>(0);
  const [treeHasError, setTreeHasError] = useState<boolean>(false);
  const [isPrintView, setIsPrintView] = useState<boolean>(false);
  const [collapsedBoxIds, setCollapsedBoxIds] = useState<string[]>([]);
  const [deletedHypothesisNames, setDeletedHypothesisNames] = useState<string[]>([]);
  const [latexSettings, setLatexSettings] = useState<LatexSettings>(DEFAULT_LATEX_SETTINGS);
  const [perfectArrows, setPerfectArrows] = useState<Arrow[]>([]);

  React.useLayoutEffect(() => {
    if (!convertedProofTree) { setPerfectArrows([]); return; }
    setPerfectArrows(createHypArrows(convertedProofTree));
  }, [convertedProofTree, latexSettings]);

  const latexSettingsForFormat = (
    converted: ConvertedProofTree,
    format: NaturalProofTree["format"]
  ): LatexSettings => {
    if (format !== "latex") return DEFAULT_LATEX_SETTINGS;
    const { stable, changing } = collectTexts(converted);
    const map: Record<string, string> = {};
    for (const text of [...stable, ...changing]) map[text] = text;
    return { ...DEFAULT_LATEX_SETTINGS, isActive: true, map };
  };

  const assertStepsDoSomething = (box: any) => {
    for (const step of box.tactics ?? []) {
      const hasDelta =
        (Array.isArray(step.newHyps) && step.newHyps.length > 0) ||
        typeof step.newGoal === "string" ||
        step.closed === true ||
        (Array.isArray(step.newSubgoals) && step.newSubgoals.length > 0) ||
        (Array.isArray(step.haveBoxes) && step.haveBoxes.length > 0);
      if (!hasDelta) {
        throw new Error(
          `Step "${step.tactic}" does nothing. Every step needs at least one of: ` +
          `newHyps, newGoal, closed, newSubgoals, haveBoxes.`
        );
      }
      (step.newSubgoals ?? []).forEach(assertStepsDoSomething);
      (step.haveBoxes ?? []).forEach(assertStepsDoSomething);
    }
  };

  const validateAndCompile = (jsonValue: string) => {
    if (!jsonValue.trim()) {
      setConvertedProofTree(null);
      setError(null);
      setIsEditing(false);
      return;
    }

    try {
      const naturalProofTree: NaturalProofTree = JSON.parse(jsonValue);

      if (Array.isArray(naturalProofTree) || typeof naturalProofTree !== 'object' || naturalProofTree === null) {
        throw new Error('Root must be a box object (with "goal", "newHyps", "tactics")');
      }
      if (typeof naturalProofTree.goal !== 'string') {
        throw new Error('Box is missing a "goal" string');
      }
      if (!Array.isArray(naturalProofTree.tactics)) {
        throw new Error('Box is missing a "tactics" array');
      }
      if (naturalProofTree.format !== "unicode" && naturalProofTree.format !== "latex") {
        throw new Error('Root box must declare "format": "unicode" or "latex"');
      }
      assertStepsDoSomething(naturalProofTree);

      const converted: ConvertedProofTree = naturalToConverted(naturalProofTree);
      converted.boxes.forEach((box) => {
        box.hypTables = hypsToTables(box.hypLayers, converted, false);
      });

      // Success - save and render; only reset the error boundary if it previously crashed
      localStorage.setItem(LS_KEY, jsonValue);
      setError(null);
      setIsEditing(false);
      setConvertedProofTree(converted);
      setLatexSettings(latexSettingsForFormat(converted, naturalProofTree.format));
      if (treeHasError) { setRenderKey(k => k + 1); setTreeHasError(false); }

    } catch (err) {
      const errorMessage = err instanceof Error ? err.message : 'Unknown error occurred';
      setError('Error: ' + errorMessage);
      setIsEditing(false);
      // Keep the last valid tree visible - don't clear convertedProofTree
    }
  };

  // Compile saved JSON on first mount
  useEffect(() => {
    const saved = localStorage.getItem(LS_KEY);
    if (saved) validateAndCompile(saved);
  }, []); // eslint-disable-line react-hooks/exhaustive-deps

  const handleValidationChange = (isValid: boolean, _markers: any[]) => {
    if (isValid) validateAndCompile(jsonInput);
    // When invalid, leave the last tree visible; isEditing is already set by handleJsonChange
  };

  const handleJsonChange = (newValue: string) => {
    setJsonInput(newValue);
    setIsEditing(true);
    setTimeout(() => validateAndCompile(newValue), 300);
  };

  const dummyCreateSnapshot = async () => "snapshot-id";

  const [copied, setCopied] = useState(false);
  const copyInstructions = async () => {
    await navigator.clipboard.writeText(llmInstructions);
    setCopied(true);
    setTimeout(() => setCopied(false), 2000);
  };

  useEffect(() => {
    const onKey = (e: KeyboardEvent) => { if (e.key === 'Escape') setIsPrintView(false); };
    window.addEventListener('keydown', onKey);
    return () => window.removeEventListener('keydown', onKey);
  }, []);

  // Glass overlay: shown while the user is mid-edit or the current JSON has an error
  const showOverlay = isEditing || (!!error && !!convertedProofTree);

  const proofTreeContent = convertedProofTree && (
    <ProofTreeErrorBoundary key={renderKey} onError={() => setTreeHasError(true)}>
      <StandaloneGlobalContext.Provider
        value={{
          UIVersion: 1,
          refreshUI: () => {},
          collapsedBoxIds,
          setCollapsedBoxIds,
          searchedHypIds: [],
          setSearchedHypIds: () => {},
          deletedHypothesisNames,
          setDeletedHypothesisNames,
          settings: {
            isSingleTacticMode: false,
            isCompactMode     : false,
            isCompactTactics  : false,
            isHiddenGoalNames : false,
            isGreenHypotheses : false,
            areHypsHighlighted: false,
          },
          setSettings: () => {},
          proofTree: convertedProofTree,
          highlights: { hypIds: [], goalId: null },
          position: { line: 0, column: 0 },
          setConverted: () => {},
          createSnapshot: dummyCreateSnapshot,
          setSnackbarMessage: () => {},
          setSnackbarOpen: () => {},
          isStandalone: true,
          fontSize: 12,
          setFontSize: () => {},
          fetchFullProofTree: async () => convertedProofTree!,
          latexSettings,
          setLatexSettings,
        }}
      >
        <div className={`proof-tree -isCompactTacticsOFF -isGreenHypothesesOFF${latexSettings.isActive ? ' -isLatexModeON' : ''}`}>
          <StandaloneProofTree />
          {perfectArrows.map((arrow, index) =>
            <PerfectArrow key={index} p1={arrow.from} p2={arrow.to}/>
          )}
        </div>
      </StandaloneGlobalContext.Provider>
    </ProofTreeErrorBoundary>
  );

  if (isPrintView) {
    return (
      <div className="natural-print-view">
        <button className="natural-print-exit" onClick={() => setIsPrintView(false)}>← back</button>
        {proofTreeContent}
      </div>
    );
  }

  return (
    <div className="natural-page">

      <Nav />

      <div className="natural-try">
        <h1>See any proof as a Paperproof tree.</h1>
        <p>
          Write a proof in natural language, then let an LLM convert it to the Paperproof JSON format.
          Paste the JSON below to render the tree.
        </p>
        <div className="natural-steps">
          <div className="natural-step">
            <span className="natural-step-n">1</span>
            <div>
              <strong>Copy the LLM instructions</strong>
              <span> - they explain the JSON format with examples.</span>
            </div>
            <button className={`natural-copy-btn${copied ? " -copied" : ""}`} onClick={copyInstructions}>
              {copied ? "Copied!" : "Copy instructions"}
            </button>
          </div>
          <div className="natural-step">
            <span className="natural-step-n">2</span>
            <div>
              <strong>Paste your natural-language proof</strong> and <strong>LLM instructions</strong>
              <span> into any LLM (Claude, DeepSeek, etc.). Ask for JSON.</span>
            </div>
          </div>
          <div className="natural-step">
            <span className="natural-step-n">3</span>
            <div>
              <strong>Paste the resulting JSON below</strong>
              <span> - the proof should render instantly.</span>
            </div>
          </div>
        </div>

        <div className="pp-panel natural-editor-wrap">
          <div className="pp-panel-tabs">
            <span className="pp-panel-tab -active">≡ proof.json ×</span>
            <button
              className="natural-load-example-btn"
              onClick={() => handleJsonChange(exampleJson)}
            >
              Load example
            </button>
          </div>
          <JsonEditor
            value={jsonInput}
            onChange={handleJsonChange}
            onValidationChange={handleValidationChange}
            height="360px"

          />
        </div>

        {!convertedProofTree && !error && (
          <div className="natural-placeholder">
            Paste valid proof JSON above - your tree will appear here.
          </div>
        )}

        {convertedProofTree && (
          <div className="pp-panel proof-tree-wrap">
            <div className="pp-panel-tabs">
              <span className="pp-panel-tab -active">≡ Paperproof ×</span>
              <span className="pp-panel-tab">≡ Lean Infoview</span>
              <button className="natural-load-example-btn" onClick={() => setIsPrintView(true)}>Print</button>
            </div>
            <div className="natural-proof-body">
              {showOverlay && <div className="natural-proof-overlay" />}
              {proofTreeContent}
            </div>
          </div>
        )}
      </div>

    </div>
  );
}

const root = createRoot(document.getElementById("root")!);
root.render(<StandaloneRenderer />);
