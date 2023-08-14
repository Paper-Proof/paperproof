import * as vscode from "vscode";
import toggleWebviewPanel from "./actions/toggleWebviewPanel";
import sendPosition from "./actions/sendPosition";
import { Shared } from "./types";

const DEFAULT_SERVER_URL = "https://paperproof.xyz";

export function activate(context: vscode.ExtensionContext) {
  const shared : Shared = {
    latestInfo: null,
    onLeanClientRestarted: null,
    webviewPanel: null,
    // Creates the 'paperproof' channel in vscode's "OUTPUT" pane
    log: vscode.window.createOutputChannel("paperproof")
  };

  // Settings
  const config = vscode.workspace.getConfiguration("paperproof");
  const SERVER_URL = config.get("serverUrl", DEFAULT_SERVER_URL);

  // Sending types to the server on cursor changes.
  //
  // These events seem to get called twice. We only need `onDidChangeTextEditorSelection`.
  // E.g., when we click on a neighbouring tab, we do get `onDidChangeTextEditorSelection` called.
  // 
  //
  // sendPosition(shared, vscode.window.activeTextEditor);
  // vscode.window.onDidChangeActiveTextEditor((textEditor) => {
  //   sendPosition(shared, textEditor);
  // });
  vscode.window.onDidChangeTextEditorSelection((event) => {
    sendPosition(shared, event.textEditor);
  });

  context.subscriptions.push(
    vscode.commands.registerCommand("paperproof.toggle", () => {
      toggleWebviewPanel(shared, SERVER_URL);
    })
  );
}

// This method is called when your extension is deactivated
export function deactivate() { }
