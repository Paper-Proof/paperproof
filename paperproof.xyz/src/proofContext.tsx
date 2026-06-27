import React from "react";
import { ConvertedProofTree, LatexSettings } from "types";

export interface StandaloneGlobalContextType {
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
  setSnackbarMessage: (message: any) => void;
  setSnackbarOpen: (open: boolean) => void;
  isStandalone: boolean;
  fontSize: number;
  setFontSize: (x: number) => void;
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
