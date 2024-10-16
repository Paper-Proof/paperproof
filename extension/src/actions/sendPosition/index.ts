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

  const body = await getResponseOrError(shared, tdp);
  if (token.isCancellationRequested) { return; }
  shared.latestInfo = body;
  await shared.webviewPanel?.webview.postMessage(body);
};

export default sendPosition;
