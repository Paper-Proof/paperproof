import * as vscode from "vscode";
import { TextDocumentPositionParams } from "vscode-languageserver-protocol";
import { Shared } from "../../types";
import getErrorMessage from "../../services/getErrorMessage";
import fetchLeanData from "./services/fetchLeanData";
import shouldIgnoreEvent from "./services/shouldIgnoreEvent";
import getLeanClient from "../../services/getLeanClient";

const getResponseOrError = async (shared: Shared, editor: vscode.TextEditor, tdp: TextDocumentPositionParams) => {
  try {
    const leanClient = await getLeanClient(shared);
    const body = await fetchLeanData(shared, leanClient, editor, tdp);
    shared.log.appendLine("🎉 Sent everything");
    return body;
  } catch (error) {
    const message = getErrorMessage(error);
    const body = { error: message };
    shared.log.appendLine(`❌ Error: "${message}"`);
    return body;
  }
};

// Best-effort: scan upward from the cursor for the enclosing declaration so we
// can name what's loading. Pure string scan — never throws, returns null if
// nothing recognizable is found.
const DECL_RE = /^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|public|protected|noncomputable|partial|scoped|local)\s+)*(theorem|lemma|def|instance|abbrev|example|structure|inductive)\b\s*([A-Za-z_][\w.'!?]*)?/;
const enclosingDeclName = (document: vscode.TextDocument, line: number): string | null => {
  for (let l = Math.min(line, document.lineCount - 1); l >= 0; l--) {
    const m = DECL_RE.exec(document.lineAt(l).text);
    if (m) { return m[2] ?? m[1]; } // name, or the keyword (e.g. "example")
  }
  return null;
};

const sendPosition = async (shared: Shared, editor: vscode.TextEditor | undefined, token: vscode.CancellationToken) => {
  if (!editor || shouldIgnoreEvent(editor)) { return; };

  let tdp = {
    textDocument: { uri: editor.document.uri.toString() },
    position: { line: editor.selection.active.line, character: editor.selection.active.character },
  };
  shared.log.appendLine(`\nText selection: ${JSON.stringify(tdp)}`);

  shared.webviewPanel?.webview.postMessage({
    type: 'from_extension:start_loading',
    data: { name: enclosingDeclName(editor.document, editor.selection.active.line) }
  });
  shared.webviewPanel?.webview.postMessage({
    type: 'from_extension:update_position',
    data: tdp.position
  });
  const body = await getResponseOrError(shared, editor, tdp);
  if (token.isCancellationRequested) { return; }
  await shared.webviewPanel?.webview.postMessage({
    type: 'from_extension:sendPosition',
    data: body
  });
};

export default sendPosition;
