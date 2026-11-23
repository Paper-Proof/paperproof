import React from "react";
import { ConvertedProofTree, Highlights, LatexSettings, Position, Settings } from "types";

declare global {
  const IS_VSCODE: boolean;
}

export interface GlobalContextType {
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
  setConverted: (x: Converted | null) => void;
  createSnapshot: () => Promise<string>;
  setSnackbarMessage: (message: String | React.ReactNode | null) => void;
  setSnackbarOpen: (open: boolean) => void;
  proofTreeRef: React.RefObject<HTMLDivElement | null>;
  fetchFullProofTree: () => Promise<ConvertedProofTree>;
  latexSettings: LatexSettings;
  setLatexSettings: (x: LatexSettings) => void;
}

export const GlobalContext = React.createContext<GlobalContextType | undefined>(undefined);

// This allows us to use `undefined` for the default GlobalContext value
// (see https://stackoverflow.com/a/69735347/3192470)
export const useGlobalContext = () => {
  const globalContext = React.useContext(GlobalContext);
  if (!globalContext)
      throw new Error('No <GlobalContext.Provider/> found when calling useGlobalContext.');
  return globalContext;
};

export interface Converted {
  proofTree: ConvertedProofTree;
  highlights: Highlights;
  statement: string | null;
}
