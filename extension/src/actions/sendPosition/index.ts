import * as vscode from "vscode";
import { Shared } from "../../types";
import getErrorMessage from "../../services/getErrorMessage";
import sendInfoAtTdp from "./services/sendInfoAtTdp";

const sendPosition = async (shared: Shared, editor: vscode.TextEditor | undefined) => {
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

    const body = { error: message };
    // Save for later sending in case there is no session for the server or no webview open yet.
    shared.latestInfo = body;
    // Send directly to the webview (if it's open!) to avoid lag
    await shared.webviewPanel?.webview.postMessage(body);
  }
};

export default sendPosition;
