import * as vscode from "vscode";
import { TextDocumentPositionParams } from "vscode-languageserver-protocol";
import { Shared } from "../../types";
import getErrorMessage from "../../services/getErrorMessage";
import fetchLeanData from "./services/fetchLeanData";
import shouldIgnoreEvent from "./services/shouldIgnoreEvent";

const getLeanClient = async (shared: Shared, editor: vscode.TextEditor) => {
  const leanExtension = vscode.extensions.getExtension("leanprover.lean4");
  if (!leanExtension) {
    throw new Error("leanExtensionNotFound");
  }

  const clientProvider = leanExtension.exports.clientProvider;
  const client = clientProvider.getActiveClient();
  if (!client) {
    throw new Error("leanClientNotFound");
  }

  if (!client.running) {
    // TODO this is desired, but temporarily disabled to debug asynchronicity
    // NOTE it looks like it works nicely without this too? Is this only useful on vscode editor startup?
    //
    // Dispose of the previous listener if there was one
    // shared.onLeanClientRestarted?.dispose();
    // shared.onLeanClientRestarted = client.restarted(() => {
    //   sendPosition(shared, editor)
    //   .then(() => {
    //     shared.onLeanClientRestarted?.dispose();
    //   });
    // });
    throw new Error("leanNotYetRunning");
  }

  return client;
};

const getResponseOrError = async (shared: Shared, editor: vscode.TextEditor, tdp: TextDocumentPositionParams) => {
  try {
    const leanClient = await getLeanClient(shared, editor);
    const body = await fetchLeanData(shared.log, leanClient, tdp);
    shared.log.appendLine("🎉 Sent everything");
    return body;
  } catch (error) {
    const message = getErrorMessage(error);
    const body = { error: message };
    shared.log.appendLine(`❌ Error: "${message}"`);
    return body;
  }
};

const sendPosition = async (shared: Shared, editor: vscode.TextEditor | undefined, token: vscode.CancellationToken) => {
  if (!editor || shouldIgnoreEvent(editor)) { return; };

  let tdp = {
    textDocument: { uri: editor.document.uri.toString() },
    position: { line: editor.selection.active.line, character: editor.selection.active.character },
  };
  shared.log.appendLine(`\nText selection: ${JSON.stringify(tdp)}`);

  const body = await getResponseOrError(shared, editor, tdp);
  if (token.isCancellationRequested) { return; }
  shared.latestInfo = body;
  await shared.webviewPanel?.webview.postMessage(body);
};

export default sendPosition;
