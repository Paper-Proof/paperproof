import * as vscode from "vscode";
import { TextDocumentPositionParams } from "vscode-languageserver-protocol";

import { ProofState, ProofError } from "./types";
import createWebviewPanel from "./services/createWebviewPanel";
import vscodeRequest from "./services/vscodeRequest";

const DEFAULT_SERVER_URL = "https://paperproof.xyz";
let SERVER_URL = DEFAULT_SERVER_URL;

let latestInfo: ProofState | ProofError | null = null;
let onLeanClientRestarted: vscode.Disposable | null = null;

const getErrorMessage = (error: unknown) => {
  if (error instanceof Error) {
    return error.message;
  }
  return String(error);
};

const sendTypes = async (
  webviewPanel: vscode.WebviewPanel | null,
  body: ProofState | ProofError
) => {
  // Save for later sending in case there is no session for the server or no webview open yet.
  latestInfo = body;
  // Send directly to the webview (if it's open!) to avoid lag
  await webviewPanel?.webview.postMessage(body);
};

const sendInfoAtTdp = async (
  log: vscode.OutputChannel,
  client: any,
  webviewPanel: vscode.WebviewPanel | null,
  tdp: TextDocumentPositionParams
) => {
  const uri = tdp.textDocument.uri;
  const proofTreeResponse = await vscodeRequest(log, "getSnapshotData", client, uri, tdp, { pos: tdp.position });
  const goalsResponse = await vscodeRequest(log, "Lean.Widget.getInteractiveGoals", client, uri, tdp, tdp);

  const body: ProofState = {
    goal: (goalsResponse && goalsResponse.goals[0]) || null,
    proofTree: proofTreeResponse.steps,
  };

  await sendTypes(webviewPanel, body);

  log.appendLine("🎉 Sent everything");
};

export function activate(context: vscode.ExtensionContext) {
  // Settings
  const config = vscode.workspace.getConfiguration("paperproof");
  console.log("Config", config);
  SERVER_URL = config.get("serverUrl", DEFAULT_SERVER_URL);

  // Creates the 'paperproof' channel in vscode's "OUTPUT" pane
  let log = vscode.window.createOutputChannel("paperproof");

  const sendPosition = async (editor: vscode.TextEditor | undefined) => {
    try {
      if (!editor) {
        return;
      }
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
      const leanExtension = vscode.extensions.getExtension("leanprover.lean4");
      if (!leanExtension) {
        throw new Error("Lean extension not found");
      }
      const clientProvider = leanExtension.exports.clientProvider;
      const [_, client] = await clientProvider.ensureClient(doc.uri, undefined);
      if (!client) {
        throw new Error("Lean client not found");
      }
      if (!client.running) {
        // Dispose of the previous listener if there was one
        onLeanClientRestarted?.dispose();
        onLeanClientRestarted = client.restarted(() => {
          sendInfoAtTdp(log, client, webviewPanel, tdp);
          onLeanClientRestarted?.dispose();
        });
        throw new Error(
          "leanNotYetRunning"
        );
      }
      log.appendLine("Found a Lean client");
      await sendInfoAtTdp(log, client, webviewPanel, tdp);
    } catch (error) {
      const message = getErrorMessage(error);
      log.appendLine(`❌ Error in sendPosition: "${message}"`);
      await sendTypes(webviewPanel, { error: message });
    }
  };

  // Sending types to the server on cursor changes.
  sendPosition(vscode.window.activeTextEditor);
  vscode.window.onDidChangeActiveTextEditor(sendPosition);
  vscode.window.onDidChangeTextEditorSelection((event) => {
    // We should ignore it when the user is selecting some range of text
    if (!event.selections[0].isEmpty) {
      return;
    }
    sendPosition(event.textEditor)
  });

  let webviewPanel: vscode.WebviewPanel | null = null;
  context.subscriptions.push(
    vscode.commands.registerCommand("paperproof.toggle", () => {
      if (webviewPanel) {
        webviewPanel.dispose();
      } else {
        webviewPanel = createWebviewPanel(SERVER_URL, latestInfo)
        webviewPanel.onDidDispose(() => { webviewPanel = null; });
      }
    })
  );
}

// This method is called when your extension is deactivated
export function deactivate() { }
