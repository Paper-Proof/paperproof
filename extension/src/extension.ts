import * as vscode from "vscode";
import toggleWebviewPanel from "./actions/toggleWebviewPanel";
import sendPosition from "./actions/sendPosition";
import { Shared } from "./types";

export function activate(context: vscode.ExtensionContext) {
  const shared : Shared = {
    context,
    latestInfo: null,
    onLeanClientRestarted: null,
    webviewPanel: null,
    // Creates the 'paperproof' channel in vscode's "OUTPUT" pane
    log: vscode.window.createOutputChannel("paperproof")
  };

  vscode.workspace.onDidChangeConfiguration((event) => {
    if (event.affectsConfiguration("paperproof.environment")) {
      // This makes the asset urls reload automatically, without any participation from the developer
      if (shared.webviewPanel) { shared.webviewPanel.dispose(); }
      toggleWebviewPanel(shared);
    }
  });

  // Sending types to the server on cursor changes.
  // We use a `cancellationToken` to make sure only the last request gets through.
  let cancellationToken: vscode.CancellationTokenSource | null = null;
  vscode.window.onDidChangeActiveTextEditor((textEditor) => {
    if (cancellationToken) { cancellationToken.cancel(); }
    cancellationToken = new vscode.CancellationTokenSource();
    sendPosition(shared, textEditor, cancellationToken.token);
  });
  vscode.window.onDidChangeTextEditorSelection((event) => {
    if (cancellationToken) { cancellationToken.cancel(); }
    cancellationToken = new vscode.CancellationTokenSource();
    sendPosition(shared, event.textEditor, cancellationToken.token);
  });

  context.subscriptions.push(
    vscode.commands.registerCommand("paperproof.toggle", () => {
      toggleWebviewPanel(shared);
    })
  );
}

// This method is called when your extension is deactivated
export function deactivate() { }
