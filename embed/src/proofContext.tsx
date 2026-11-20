import React from "react";
import { ConvertedProofTree, Highlights, LatexSettings, Position, Settings } from "types";

// Stands in for src/indexBrowser's context (build.mjs redirects the import), which calls acquireVsCodeApi() and throws outside vscode
export interface StandaloneGlobalContextType {
  UIVersion: number;
  refreshUI: () => void;
  collapsedBoxIds: string[];
  setCollapsedBoxIds: (x: string[]) => void;
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
  proofTreeRef: React.RefObject<HTMLDivElement | null>;
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
