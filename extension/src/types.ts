import * as vscode from "vscode";

export interface ProofState {
  goal: any;
  proofTree: any;
  version?: number;
}

export interface ProofError {
  error: string;
}

export type ProofStateOrError = ProofState | ProofError;

export interface Shared {
  context: vscode.ExtensionContext;
  onLeanClientRestarted: vscode.Disposable | null;
  webviewPanel: vscode.WebviewPanel | null;
  log: vscode.OutputChannel;
}
