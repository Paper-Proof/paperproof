import * as vscode from "vscode";
import { Shared } from "../../types";
import getErrorMessage from "../../services/getErrorMessage";
import getLeanData from "./services/getLeanData";
import shouldIgnoreEvent from "./services/shouldIgnoreEvent";

const sendPosition = async (shared: Shared, editor: vscode.TextEditor | undefined) => {
  try {
    if (!editor || shouldIgnoreEvent(editor)) { return; };

    const selection = editor.selection.active;
    let tdp = {
      textDocument: { uri: editor.document.uri.toString() },
      position: { line: selection.line, character: selection.character },
    };
    shared.log.appendLine("");
    shared.log.appendLine(`Text selection: ${JSON.stringify(tdp)}`);
    const leanExtension = vscode.extensions.getExtension("leanprover.lean4");
    if (!leanExtension) {
      throw new Error("Lean extension not found");
    }
    const clientProvider = leanExtension.exports.clientProvider;
    const [_, client] = await clientProvider.ensureClient(editor.document.uri, undefined);
    if (!client) {
      throw new Error("Lean client not found");
    }
    if (!client.running) {
      // Dispose of the previous listener if there was one
      shared.onLeanClientRestarted?.dispose();
      shared.onLeanClientRestarted = client.restarted(() => {
        getLeanData(shared.log, client, tdp);
        shared.onLeanClientRestarted?.dispose();
      });
      throw new Error("leanNotYetRunning");
    }
    shared.log.appendLine("Found a Lean client");
    const body = await getLeanData(shared.log, client, tdp);
    // Save for later sending in case there is no session for the server or no webview open yet.
    shared.latestInfo = body;
    // Send directly to the webview (if it's open!) to avoid lag
    await shared.webviewPanel?.webview.postMessage(body);

    shared.log.appendLine("🎉 Sent everything");
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
