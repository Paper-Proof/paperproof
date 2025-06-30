import * as vscode from "vscode";
import toggleWebviewPanel from "./actions/toggleWebviewPanel";
import sendPosition from "./actions/sendPosition";
import { Shared } from "./types";
import Settings from "./services/Settings";

export function activate(context: vscode.ExtensionContext) {
  const shared : Shared = {
    context,
    onLeanClientRestarted: null,
    webviewPanel: null,
    // Creates the 'paperproof' channel in vscode's "OUTPUT" pane
    log: vscode.window.createOutputChannel("paperproof")
  };

  vscode.workspace.onDidChangeConfiguration((event) => {
    Settings.updateSettingsFromExtension(event, shared)
  });

  // Sending types to the server on cursor changes.
  // We use a `cancellationToken` to make sure only the last request gets through.
  let cancellationToken: vscode.CancellationTokenSource | null = null;

  const fetchInfoTree = (textEditor: vscode.TextEditor | undefined) => {
    // Our parser is expensive - don't run it unless the Papeproof panel is open
    // (see https://github.com/Paper-Proof/paperproof/issues/51#issuecomment-2408463605)
    if (!shared.webviewPanel) { return; }

    if (cancellationToken) { cancellationToken.cancel(); }
    cancellationToken = new vscode.CancellationTokenSource();
    sendPosition(shared, textEditor, cancellationToken.token);
  };

  vscode.window.onDidChangeActiveTextEditor((textEditor) => {
    fetchInfoTree(textEditor);
  });
  vscode.window.onDidChangeTextEditorSelection((event) => {
    fetchInfoTree(event.textEditor);
  });

  context.subscriptions.push(
    vscode.commands.registerCommand("paperproof.toggle", () => {
      toggleWebviewPanel(shared);
    })
  );
}

// This method is called when your extension is deactivated
export function deactivate() { }
