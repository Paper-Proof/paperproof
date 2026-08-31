import React from "react";
import { ConvertedProofTree, Highlights, LatexSettings, Position, Settings } from "types";

/**
 * [Claude comment]
 * `/app` imports its context from `src/indexBrowser`, which calls
 * `acquireVsCodeApi()` at module scope and would throw in a normal browser tab.
 * `esbuild.js` redirects that import here, so this must mirror the same context
 * minus anything that talks to vscode.
 */
export interface StandaloneGlobalContextType {
  UIVersion: number;
  refreshUI: () => void;
  collapsedBoxIds: string[];
  setCollapsedBoxIds: (x: string[]) => void;
  searchedHypIds: string[];
  setSearchedHypIds: (x: string[]) => void;
  deletedHypothesisNames: string[];
  setDeletedHypothesisNames: (x: string[]) => void;
  settings: Settings;
  setSettings: (x: Settings) => void;
  proofTree: ConvertedProofTree;
  highlights: Highlights;
  position: Position;
  setConverted: (x: any) => void;
  createSnapshot: () => Promise<string>;
  setSnackbarMessage: (message: any) => void;
  setSnackbarOpen: (open: boolean) => void;
  isStandalone: boolean;
  fetchFullProofTree: () => Promise<ConvertedProofTree>;
  latexSettings: LatexSettings;
  setLatexSettings: (x: LatexSettings) => void;
}

export const StandaloneGlobalContext = React.createContext<StandaloneGlobalContextType | undefined>(undefined);

export const useStandaloneGlobalContext = () => {
  const ctx = React.useContext(StandaloneGlobalContext);
  if (!ctx) throw new Error("No <StandaloneGlobalContext.Provider/> found.");
  return ctx;
};

export const useGlobalContext = useStandaloneGlobalContext;
export type GlobalContextType = StandaloneGlobalContextType;
