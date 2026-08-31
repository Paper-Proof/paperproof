import * as vscode from "vscode";
import toggleWebviewPanel from "./actions/toggleWebviewPanel";
import sendPosition from "./actions/sendPosition";
import { Shared } from "./types";
import Settings from "./services/Settings";
import { disposeShadowDoc, disposeAllShadowDocs } from "./services/noInstall/shadowDoc";

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

  // Cursor moves (clicks) -> re-query immediately. In no-install mode this hits
  // an already-elaborated shadow document, so it stays fast.
  vscode.window.onDidChangeActiveTextEditor((textEditor) => {
    fetchInfoTree(textEditor);
  });
  vscode.window.onDidChangeTextEditorSelection((event) => {
    fetchInfoTree(event.textEditor);
  });

  // Edits -> the shadow goes stale; debounce a refresh so we re-elaborate once
  // the user pauses, not on every keystroke (this is the "hybrid" boundary).
  let editDebounce: ReturnType<typeof setTimeout> | null = null;
  vscode.workspace.onDidChangeTextDocument((event) => {
    const editor = vscode.window.activeTextEditor;
    if (!editor || event.document !== editor.document) { return; }
    if (editDebounce) { clearTimeout(editDebounce); }
    editDebounce = setTimeout(() => fetchInfoTree(editor), 300);
  });

  // Clean up the shadow document when its source file is closed.
  vscode.workspace.onDidCloseTextDocument((doc) => {
    disposeShadowDoc(doc.uri.toString());
  });

  context.subscriptions.push(
    vscode.commands.registerCommand("paperproof.toggle", () => {
      toggleWebviewPanel(shared);
    })
  );
}

// This method is called when your extension is deactivated
export function deactivate() {
  disposeAllShadowDocs();
}
