import * as vscode from "vscode";
import { TextDocumentPositionParams } from "vscode-languageserver-protocol";
import fetch from "node-fetch";
// @ts-ignore
import converter from "./converter";

const SERVER_URL = "https://paperproof.xyz";
let sessionId: string | null = null;
let latestInfo: object | null = null;

const getErrorMessage = (error: unknown) => {
  if (error instanceof Error) {
    return error.message;
  }
  return String(error);
};

const sendTypesToServer = async (sessionId: string, body: object) =>
  fetch(`${SERVER_URL}/sendTypes?sessionId=${sessionId}`, {
    method: "POST",
    // eslint-disable-next-line @typescript-eslint/naming-convention
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify(body),
  });

const sendTypes = async (
  webviewPanel: vscode.WebviewPanel | null,
  body: object
) => {
  // Save for the later sending in case there is no session for the server or no webview open yet.
  latestInfo = body;

  // 1. Send directly to the webview (if it's open!) to avoid lag
  webviewPanel?.webview.postMessage(body);

  // 2. After that, send data to .xyz
  if (sessionId) {
    sendTypesToServer(sessionId, body);
  }
};

// Simple request. We don't keep session open and create a new one for each request for now.
const vscodeRequest = async (
  log: vscode.OutputChannel,
  method: string,
  client: any,
  uri: string,
  tdp: TextDocumentPositionParams,
  params: any
): Promise<any> => {
  log.appendLine(`Making ${method} request`);
  const connection = await client.sendRequest("$/lean/rpc/connect", { uri });
  const response = await client.sendRequest("$/lean/rpc/call", {
    sessionId: connection.sessionId,
    method,
    // These are always needed for Lean rpcs
    // (https://github.com/leanprover/lean4/blob/367b38701fb9cca80328624a016c3b3acfd5e2cd/src/Lean/Data/Lsp/Basic.lean#L288)
    ...tdp,
    params,
  });
  return response;
};

function getWebviewContent(initialInfo: object | null) {
  return `
  <!DOCTYPE html>
  <html lang="en">
    <head>
      <meta charset="UTF-8">
      <meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover"/>
      <title>Paperproof</title>
    </head>
    <body>
      <script>initialInfo = ${initialInfo}</script>
      <div id="root"></div>
      <script src="${SERVER_URL}/indexBrowser.js"></script>
    </body>
  </html>`;
}

const sendInfoAtCurrentPos = async (
  log: vscode.OutputChannel,
  webviewPanel: vscode.WebviewPanel | null,
  editor: vscode.TextEditor
) => {
  const doc = editor.document;
  if (doc.languageId !== "lean4" && doc.languageId !== "lean") {
    return;
  }
  const pos = editor.selection.active;
  let tdp = {
    textDocument: { uri: doc.uri.toString() },
    position: { line: pos.line, character: pos.character },
  };
  log.appendLine("");
  log.appendLine(`Text selection: ${JSON.stringify(tdp)}`);
  const uri = tdp.textDocument.uri;
  const leanExtension = vscode.extensions.getExtension("leanprover.lean4");
  if (!leanExtension) {
    return;
  }
  const clientProvider = leanExtension.exports.clientProvider;
  const client = clientProvider.findClient(uri);
  if (!client) {
    return;
  }
  log.appendLine("Found a Lean client");

  const proofTreeResponse = await vscodeRequest(
    log,
    "getPpContext",
    client,
    uri,
    tdp,
    { pos: tdp.position }
  );
  const goalsResponse = await vscodeRequest(
    log,
    "Lean.Widget.getInteractiveGoals",
    client,
    uri,
    tdp,
    tdp
  );

  const body = {
    goal: (goalsResponse && goalsResponse.goals[0]) || null,
    statement: proofTreeResponse.statement,
    proofTree: converter(proofTreeResponse.steps),
    // TODO: This is only for development, comment out this line for production (bc it's lengthy)
    leanProofTree: proofTreeResponse.steps,
  };

  await sendTypes(webviewPanel, body);

  log.appendLine("🎉 Sent everything");
};

function showNotification(sessionId: string) {
  const url = `${SERVER_URL}/${sessionId}`;
  const openButton: vscode.MessageItem = { title: "Open in browser" };
  vscode.window
    .showInformationMessage(`Your session is available at ${url}`, openButton)
    .then((selectedItem) => {
      if (selectedItem === openButton) {
        vscode.env.openExternal(vscode.Uri.parse(url));
      }
    });
}

export function activate(context: vscode.ExtensionContext) {
  // Creates the 'paperproof' channel in vscode's "OUTPUT" pane
  let log = vscode.window.createOutputChannel("paperproof");
  let webviewPanel: vscode.WebviewPanel | null = null;

  // Creating a new paperproof working session
  fetch(`${SERVER_URL}/newSession`, { method: "POST" })
    .then((response) => response.json())
    .then((res: any) => {
      log.appendLine(`🎉 New session: ${res.sessionId}`);
      sessionId = res.sessionId;
      if (latestInfo) {
        sendTypesToServer(res.sessionId, latestInfo).then(() => {
          log.appendLine("🎉 Pending types sent");
        });
      }
      showNotification(res.sessionId);
    });

  // Sending types to the server on cursor changes.
  vscode.window.onDidChangeTextEditorSelection(async (event) => {
    try {
      await sendInfoAtCurrentPos(log, webviewPanel, event.textEditor);
    } catch (error) {
      const message = getErrorMessage(error);
      log.appendLine(
        `❌ Error in onDidChangeTextEditorSelection: "${message}"`
      );
      await sendTypes(webviewPanel, { error: message });
    }
  });

  // Opening/hiding webviewPanel.
  function openPanel() {
    webviewPanel = vscode.window.createWebviewPanel(
      "paperproof",
      "Paper Proof",
      { viewColumn: vscode.ViewColumn.Two, preserveFocus: true },
      { enableScripts: true, retainContextWhenHidden: true }
    );
    webviewPanel.onDidDispose(() => {
      webviewPanel = null;
    });
    webviewPanel.webview.html = getWebviewContent(latestInfo);
  }
  const disposable = vscode.commands.registerCommand(
    "paperproof.toggle",
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
export function deactivate() { }
