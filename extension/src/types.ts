import * as vscode from "vscode";

export interface ProofState {
  goal: any;
  proofTree: any;
}

export interface ProofError {
  error: string;
  // [Claude comment] Extra data a specific error wants to show the user, so the
  // error string itself stays a bare code the webview can match with ===.
  meta?: Record<string, any>;
}

export type ProofStateOrError = ProofState | ProofError;

export interface Shared {
  context: vscode.ExtensionContext;
  onLeanClientRestarted: vscode.Disposable | null;
  webviewPanel: vscode.WebviewPanel | null;
  log: vscode.OutputChannel;
}
