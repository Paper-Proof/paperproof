import * as vscode from "vscode";
import toggleWebviewPanel from "./actions/toggleWebviewPanel";
import sendPosition from "./actions/sendPosition";
import { Shared } from "./types";

const DEFAULT_SERVER_URL = "https://paperproof.xyz";

export function activate(context: vscode.ExtensionContext) {
  const shared : Shared = {
    context,
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
      const isBrightTheme = vscode.window.activeColorTheme.kind === vscode.ColorThemeKind.Light;
      toggleWebviewPanel(shared, SERVER_URL, isBrightTheme);
    })
  );
}

// This method is called when your extension is deactivated
export function deactivate() { }
