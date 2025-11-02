import React, { useState } from "react";
import { createRoot } from 'react-dom/client';
import { ConvertedProofTree, LeanProofTree } from "types";
import { UserProofTree } from "types/UserProofTree";
import "./index.css";
import converter from "./services/converter";
import hypsToTables from "./services/hypsToTables";
import { convertUserProofTreeToLean } from "./services/userToLeanProofTreeConverter";

// Mock the indexBrowser module to avoid VS Code dependencies
(window as any).acquireVsCodeApi = () => ({});

import BoxEl from "./components/ProofTree/components/BoxEl";

interface StandaloneGlobalContextType {
  UIVersion: number;
  refreshUI: () => void;
  collapsedBoxIds: string[];
  setCollapsedBoxIds: (x: string[]) => void;
  searchedHypIds: string[];
  setSearchedHypIds: (x: string[]) => void;
  deletedHypothesisNames: string[];
  setDeletedHypothesisNames: (x: string[]) => void;
  settings: any;
  setSettings: (x: any) => void;
  proofTree: ConvertedProofTree;
  highlights: any;
  position: any;
  setConverted: (x: any) => void;
  createSnapshot: () => Promise<string>;
}

const StandaloneGlobalContext = React.createContext<StandaloneGlobalContextType | undefined>(undefined);

export const useStandaloneGlobalContext = () => {
  const globalContext = React.useContext(StandaloneGlobalContext);
  if (!globalContext)
    throw new Error('No <StandaloneGlobalContext.Provider/> found when calling useStandaloneGlobalContext.');
  return globalContext;
};

// Re-export this as useGlobalContext for compatibility with existing components
export const useGlobalContext = useStandaloneGlobalContext;

// Standalone ProofTree component that uses the standalone context
const StandaloneProofTree = () => {
  const { proofTree } = useStandaloneGlobalContext();
  const rootBox = proofTree.boxes.find((box) => box.parentId === null);
  if (!rootBox) return null;

  return <BoxEl box={rootBox} />;
};

function StandaloneRenderer() {
  const [jsonInput, setJsonInput] = useState<string>("");
  const [convertedProofTree, setConvertedProofTree] = useState<ConvertedProofTree | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [collapsedBoxIds, setCollapsedBoxIds] = useState<string[]>([]);
  const [deletedHypothesisNames, setDeletedHypothesisNames] = useState<string[]>([]);

  const handleRender = () => {
    try {
      setError(null);
      if (!jsonInput.trim()) {
        setError('Please paste some JSON data first.');
        return;
      }
      const userProofTree: UserProofTree = JSON.parse(jsonInput);
      const leanProofTree: LeanProofTree = convertUserProofTreeToLean(userProofTree);
      const converted: ConvertedProofTree = converter(leanProofTree);
      converted.boxes.forEach((box) => {
        box.hypTables = hypsToTables(box.hypLayers, converted, false);
      });
      setConvertedProofTree(converted);
    } catch (err) {
      const errorMessage = err instanceof Error ? err.message : 'Unknown error occurred';
      setError('Error rendering proof: ' + errorMessage);
      console.error('Full error:', err);
    }
  };

  const dummyCreateSnapshot = async () => {
    return "snapshot-id";
  };

  return (
    <div>
      <div>
        <h1>PaperProof Standalone Renderer</h1>
        <p>Paste your simplified proof tree JSON below to visualize the proof:</p>
        
        <textarea
          value={jsonInput}
          onChange={(e) => setJsonInput(e.target.value)}
          placeholder="Paste your simplified proof tree JSON here..."
        />
        
        <button onClick={handleRender}>Render Proof</button>
      </div>

      <div>
        {error && <div>{error}</div>}
        
        {!error && !convertedProofTree && (
          <div>Click "Render Proof" to visualize your proof tree.</div>
        )}
        
        {convertedProofTree && (
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
            }}
          >
            <div className={`
              proof-tree
              -isCompactTacticsOFF
              -isGreenHypothesesOFF
            `}>
              <StandaloneProofTree />
            </div>
          </StandaloneGlobalContext.Provider>
        )}
      </div>
    </div>
  );
}

const root = createRoot(document.getElementById("root")!);
root.render(<StandaloneRenderer />);