import * as vscode from "vscode";
import { Shared } from "../../types";
import getWebviewContent from './services/getWebviewContent';

const toggleWebviewPanel = (shared: Shared) => {
  if (shared.webviewPanel) {
    shared.webviewPanel.dispose();
  } else {
    const webviewPanel = vscode.window.createWebviewPanel(
      "paperproof",
      "Paperproof",
      { viewColumn: vscode.ViewColumn.Two, preserveFocus: true },
      { enableScripts: true, retainContextWhenHidden: true }
    );
    webviewPanel.webview.html = getWebviewContent(shared, webviewPanel, shared.latestInfo);
    webviewPanel.onDidDispose(() => { shared.webviewPanel = null; });
    shared.webviewPanel = webviewPanel;
  }
};

export default toggleWebviewPanel;
