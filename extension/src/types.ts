import * as vscode from "vscode";

export interface ProofState {
  goal: any;
  proofTree: any;
}

export interface ProofError {
  error: string;
}

export interface Shared {
  latestInfo: ProofState | ProofError | null;
  onLeanClientRestarted: vscode.Disposable | null;
  webviewPanel: vscode.WebviewPanel | null;
  log: vscode.OutputChannel;
}
