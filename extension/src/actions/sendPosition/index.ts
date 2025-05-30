import * as vscode from "vscode";
import { TextDocumentPositionParams } from "vscode-languageserver-protocol";
import { Shared } from "../../types";
import getErrorMessage from "../../services/getErrorMessage";
import fetchLeanData from "./services/fetchLeanData";
import shouldIgnoreEvent from "./services/shouldIgnoreEvent";
import getLeanClient from "../../services/getLeanClient";

const getResponseOrError = async (shared: Shared, tdp: TextDocumentPositionParams) => {
  try {
    const leanClient = await getLeanClient(shared);
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

  shared.webviewPanel?.webview.postMessage({
    type: 'from_extension:start_loading'
  });
  shared.webviewPanel?.webview.postMessage({
    type: 'from_extension:update_position',
    data: tdp.position
  });
  const body = await getResponseOrError(shared, tdp);
  if (token.isCancellationRequested) { return; }
  await shared.webviewPanel?.webview.postMessage({
    type: 'from_extension:sendPosition',
    data: body
  });
};

export default sendPosition;
