import * as vscode from "vscode";
import { Shared } from "../../types";
import getLeanClient from "../../services/getLeanClient";
import vscodeRequest from "../../services/vscodeRequest";
import getErrorMessage from "../../services/getErrorMessage";

const sendFullProofTree = async (shared: Shared) => {
  const editor = vscode.window.visibleTextEditors[0];
  if (!editor) return;

  const tdp = {
    textDocument: { uri: editor.document.uri.toString() },
    position: { line: editor.selection.active.line, character: editor.selection.active.character },
  };

  try {
    const leanClient = await getLeanClient(shared);
    const proofTreeResponse = await vscodeRequest(shared.log, "Paperproof.getSnapshotData", leanClient, tdp.textDocument.uri, tdp, { pos: tdp.position, mode: 'tree' });
    shared.webviewPanel?.webview.postMessage({
      type: 'from_extension:full_proof_tree',
      data: { proofTree: proofTreeResponse.steps, version: proofTreeResponse.version ?? undefined }
    });
  } catch (error) {
    shared.webviewPanel?.webview.postMessage({
      type: 'from_extension:full_proof_tree',
      data: { error: getErrorMessage(error) }
    });
  }
};

export default sendFullProofTree;
