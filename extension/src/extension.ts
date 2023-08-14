import * as vscode from "vscode";

import { ProofState, ProofError, Shared } from "./types";
import createWebviewPanel from "./services/createWebviewPanel";
import sendPosition from "./services/sendPosition";

const DEFAULT_SERVER_URL = "https://paperproof.xyz";

export function activate(context: vscode.ExtensionContext) {
  // Let's continue with making this shared.
  const shared : Shared = {
    latestInfo: null,
    onLeanClientRestarted: null,
    webviewPanel: null,
    log: vscode.window.createOutputChannel("paperproof")
  };

  // Settings
  const config = vscode.workspace.getConfiguration("paperproof");
  const SERVER_URL = config.get("serverUrl", DEFAULT_SERVER_URL);

  // Creates the 'paperproof' channel in vscode's "OUTPUT" pane
  // TODO return our logs!
  // let log = vscode.window.createOutputChannel("paperproof");

  // Sending types to the server on cursor changes.
  sendPosition(shared, vscode.window.activeTextEditor);
  vscode.window.onDidChangeActiveTextEditor((textEditor) => sendPosition(shared, textEditor));
  vscode.window.onDidChangeTextEditorSelection((event) => {
    // We should ignore it when the user is selecting some range of text
    if (!event.selections[0].isEmpty) {
      return;
    }
    sendPosition(shared, event.textEditor);
  });

  context.subscriptions.push(
    vscode.commands.registerCommand("paperproof.toggle", () => {
      if (shared.webviewPanel) {
        shared.webviewPanel.dispose();
      } else {
        shared.webviewPanel = createWebviewPanel(SERVER_URL, shared.latestInfo)
        shared.webviewPanel.onDidDispose(() => { shared.webviewPanel = null; });
      }
    })
  );
}

// This method is called when your extension is deactivated
export function deactivate() { }
