import * as vscode from "vscode";
import getWebviewContent from "./getWebviewContent";
import { ProofState, ProofError } from "../types";

function createWebviewPanel(serverUrl: string, latestInfo: ProofState | ProofError | null) {
  const webviewPanel = vscode.window.createWebviewPanel(
    "paperproof",
    "Paper Proof",
    { viewColumn: vscode.ViewColumn.Two, preserveFocus: true },
    { enableScripts: true, retainContextWhenHidden: true }
  );
  webviewPanel.webview.html = getWebviewContent(serverUrl, latestInfo);
  return webviewPanel;
}

export default createWebviewPanel;
