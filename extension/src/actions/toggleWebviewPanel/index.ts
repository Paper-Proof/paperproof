import * as vscode from "vscode";
import { Shared } from "../../types";
import getWebviewContent from './services/getWebviewContent';
import Settings from "../../services/Settings";
import sendPosition from "../sendPosition";

const toggleWebviewPanel = (shared: Shared) => {
  if (shared.webviewPanel) {
    shared.webviewPanel.dispose();
  } else {
    const webviewPanel = vscode.window.createWebviewPanel(
      "paperproof",
      "Paperproof",
      { viewColumn: vscode.ViewColumn.Two, preserveFocus: true },
      { enableScripts: true, retainContextWhenHidden: true },
    );
    webviewPanel.webview.html = getWebviewContent(shared, webviewPanel);

    webviewPanel.webview.onDidReceiveMessage(Settings.updateSettingsFromWebview);

    // This is a must, this lets us open&close paperproof panel multiple times. Also reacts to closing the tab via pressing "x".
    webviewPanel.onDidDispose(() => { 
      shared.webviewPanel = null;
    });

    shared.webviewPanel = webviewPanel;

    if (vscode.window.visibleTextEditors[0]) {
      sendPosition(shared, vscode.window.visibleTextEditors[0], (new vscode.CancellationTokenSource()).token);
    }
  }
};

export default toggleWebviewPanel;
