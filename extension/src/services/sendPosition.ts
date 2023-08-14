import * as vscode from "vscode";
import { TextDocumentPositionParams } from "vscode-languageserver-protocol";
import { ProofState, ProofError, Shared } from "../types";
import vscodeRequest from "./vscodeRequest";

const getErrorMessage = (error: unknown) => {
  if (error instanceof Error) {
    return error.message;
  }
  return String(error);
};

const sendTypes = async (
  shared : Shared,
  webviewPanel: vscode.WebviewPanel | null,
  body: ProofState | ProofError
) => {
  // Save for later sending in case there is no session for the server or no webview open yet.
  shared.latestInfo = body;
  // Send directly to the webview (if it's open!) to avoid lag
  await webviewPanel?.webview.postMessage(body);
};


const sendInfoAtTdp = async (
  shared: Shared,
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

  await sendTypes(shared, webviewPanel, body);

  log.appendLine("🎉 Sent everything");
};


const sendPosition = async (shared : Shared, editor: vscode.TextEditor | undefined) => {
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
    shared.log.appendLine("");
    shared.log.appendLine(`Text selection: ${JSON.stringify(tdp)}`);
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
      shared.onLeanClientRestarted?.dispose();
      shared.onLeanClientRestarted = client.restarted(() => {
        sendInfoAtTdp(shared, shared.log, client, shared.webviewPanel, tdp);
        shared.onLeanClientRestarted?.dispose();
      });
      throw new Error(
        "leanNotYetRunning"
      );
    }
    shared.log.appendLine("Found a Lean client");
    await sendInfoAtTdp(shared, shared.log, client, shared.webviewPanel, tdp);
  } catch (error) {
    const message = getErrorMessage(error);
    shared.log.appendLine(`❌ Error in sendPosition: "${message}"`);
    await sendTypes(shared, shared.webviewPanel, { error: message });
  }
};

export default sendPosition;
