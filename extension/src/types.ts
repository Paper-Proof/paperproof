import * as vscode from "vscode";

export interface ProofState {
  goal: any;
  proofTree: any;
}

export interface ProofError {
  error: string;
}

// It can only be `null` in the `window.initialInfo`.
export type ProofStateOrError = ProofState | ProofError | null;

export interface Shared {
  context: vscode.ExtensionContext;
  latestInfo: ProofStateOrError;
  onLeanClientRestarted: vscode.Disposable | null;
  webviewPanel: vscode.WebviewPanel | null;
  log: vscode.OutputChannel;
}
