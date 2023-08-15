import * as vscode from "vscode";

export interface ProofState {
  goal: any;
  proofTree: any;
}

export interface ProofError {
  error: string;
}

export type ProofStateOrError = ProofState | ProofError | null;

export interface Shared {
  latestInfo: ProofStateOrError;
  onLeanClientRestarted: vscode.Disposable | null;
  webviewPanel: vscode.WebviewPanel | null;
  log: vscode.OutputChannel;
}
