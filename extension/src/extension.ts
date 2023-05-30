import * as vscode from "vscode";
import { TextDocumentPositionParams } from "vscode-languageserver-protocol";
import fetch from "node-fetch";

// Simple request. We don't keep session open and create a new one for each request for now.
async function simpleRequest(
  clientProvider: any,
  uri: string,
  tdp: TextDocumentPositionParams
): Promise<any> {
  const client = clientProvider.findClient(uri);
  const conn = await client.sendRequest("$/lean/rpc/connect", {
    uri,
  });
  return client.sendRequest("$/lean/rpc/call", {
    sessionId: conn.sessionId,
    method: "getPpContext",
    ...tdp,
    params: { pos: tdp.position },
  });
}

function getWebviewContent() {
  return `
  <!DOCTYPE html>
  <html lang="en">
    <head>
      <meta charset="UTF-8">
      <meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover" />
      <title>Tactic Tree</title>
      <style>
        html, body {
          height: 100%;
        }
        body {
          padding: 0;
        }
        * { line-height: 0; }
        iframe { border: none; }
      </style>
    </head>
    <body>
      <iframe src="http://localhost:3000" width=100% height=100%></iframe>
    </body>
  </html>`;
}

export function activate(context: vscode.ExtensionContext) {
  // 1. Sending types to the server on cursor changes.
  vscode.window.onDidChangeTextEditorSelection(async (e) => {
    const editor = e.textEditor;
    const doc = editor.document;
    const pos = e.selections[0].active;
    let tdp = {
      textDocument: { uri: doc.uri.toString() },
      position: { line: pos.line, character: pos.character },
    };

    const clientProvider =
      vscode.extensions.getExtension("leanprover.lean4")?.exports
        .clientProvider;
    const context = await simpleRequest(
      clientProvider,
      tdp.textDocument.uri,
      tdp
    );
    console.log('Helllo ooo');
    await fetch("http://localhost:3000/sendTypes", {
      method: "POST",
      // eslint-disable-next-line @typescript-eslint/naming-convention
      headers: { "Content-Type": "application/json" },
      body: context as string,
    });
  });

  // 2. Opening/hiding webviewPanel.
  let webviewPanel: vscode.WebviewPanel | null = null;
  function openPanel() {
    webviewPanel = vscode.window.createWebviewPanel(
      "tactictree",
      "Tactic Tree",
      { viewColumn: vscode.ViewColumn.Two, preserveFocus: true },
      { enableScripts: true, retainContextWhenHidden: true }
    );
    webviewPanel.onDidDispose(() => {
      webviewPanel = null;
    });
    webviewPanel.webview.html = getWebviewContent();
  }
  const disposable = vscode.commands.registerCommand(
    "tactictree.toggle",
    () => {
      if (webviewPanel) {
        webviewPanel.dispose();
      } else {
        openPanel();
      }
    }
  );
  context.subscriptions.push(disposable);
}

// This method is called when your extension is deactivated
export function deactivate() {}
