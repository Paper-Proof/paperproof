import React, { useState } from "react";
import { createRoot } from 'react-dom/client';
import { ConvertedProofTree } from "types";
import "./index.css";
import converter from "./services/converter";
import hypsToTables from "./services/hypsToTables";
import { convertUserProofTreeToLean } from "./services/userToLeanProofTreeConverter";
import JsonEditor from "./components/JsonEditor";

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
  setSnackbarMessage: (message: String | React.ReactNode | null) => void;
  setSnackbarOpen: (open: boolean) => void;
  isStandalone: boolean;
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

  // Manual validation function to check if JSON is valid
  const validateAndCompile = (jsonValue: string) => {
    console.log('validateAndCompile called with:', jsonValue.substring(0, 100) + '...');
    
    if (!jsonValue.trim()) {
      setConvertedProofTree(null);
      setError(null);
      return;
    }

    try {
      // Try parsing as JSON first
      const userProofTree = JSON.parse(jsonValue);
      console.log('JSON parsed successfully:', userProofTree);
      
      // Basic validation - check if it's an array
      if (!Array.isArray(userProofTree)) {
        throw new Error('Root must be an array');
      }
      
      // Check basic structure of first tactic if present
      if (userProofTree.length > 0) {
        const firstTactic = userProofTree[0];
        if (!firstTactic.tacticString || !firstTactic.goalBefore || !firstTactic.goalsAfter) {
          throw new Error('Invalid tactic structure');
        }
      }
      
      setError(null);
      
      // Convert to LeanProofTree format
      const leanProofTree = convertUserProofTreeToLean(userProofTree);
      const converted: ConvertedProofTree = converter(leanProofTree);
      converted.boxes.forEach((box) => {
        box.hypTables = hypsToTables(box.hypLayers, converted, false);
      });
      setConvertedProofTree(converted);
      
      console.log('Successfully compiled proof tree!');
      
    } catch (err) {
      const errorMessage = err instanceof Error ? err.message : 'Unknown error occurred';
      console.log('Validation/compilation failed:', errorMessage);
      setError('Error: ' + errorMessage);
      setConvertedProofTree(null);
    }
  };

  // Auto-compile proof tree when JSON is valid (Monaco callback)
  const handleValidationChange = (isValid: boolean, markers: any[]) => {
    if (isValid) {
      // If Monaco says it's valid, try to compile
      validateAndCompile(jsonInput);
    } else {
      // Clear proof tree when Monaco says it's invalid
      setConvertedProofTree(null);
    }
  };

  // Handle direct JSON input changes (fallback)
  const handleJsonChange = (newValue: string) => {
    setJsonInput(newValue);
    
    // Debounced validation as fallback if Monaco doesn't trigger
    setTimeout(() => {
      validateAndCompile(newValue);
    }, 300); // Wait 300ms for user to stop typing
  };
  const dummyCreateSnapshot = async () => {
    return "snapshot-id";
  };

  return (
    <div>
      <section>
        <h1>Paperproof</h1>
        <p>Paste your JSON below to visualize any proof:</p>
  
        <JsonEditor
          value={jsonInput}
          onChange={handleJsonChange}
          onValidationChange={handleValidationChange}
          height="400px"
          theme="solarized-light"
        />
      </section>

      <section>
        {error && <div>{error}</div>}
        
        {!error && !convertedProofTree && (
          <div>Enter valid JSON above to see your proof tree visualization.</div>
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
              setSnackbarMessage: () => {}, // Dummy function - no snackbar in standalone
              setSnackbarOpen: () => {}, // Dummy function - no snackbar in standalone
              isStandalone: true,
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
      </section>
    </div>
  );
}

const root = createRoot(document.getElementById("root")!);
root.render(<StandaloneRenderer />);