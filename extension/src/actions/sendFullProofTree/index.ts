import * as vscode from "vscode";
import { Shared } from "../../types";
import getLeanClient from "../../services/getLeanClient";
import getErrorMessage from "../../services/getErrorMessage";
import { getShadowDoc } from "../../services/noInstall/shadowDoc";

const sendFullProofTree = async (shared: Shared) => {
  const editor = vscode.window.visibleTextEditors[0];
  if (!editor) return;

  try {
    const leanClient = await getLeanClient(shared);
    const shadow = getShadowDoc(shared.context, shared.log, leanClient, editor.document);
    if (!shadow) {
      throw new Error("noLeanProject");
    }
    // [Claude comment] tree mode regardless of the user's single-tactic setting - the whole
    // proof is what latex conversion needs
    const result = await shadow.query(editor.selection.active, false);
    shared.webviewPanel?.webview.postMessage({
      type: 'from_extension:full_proof_tree',
      data: { proofTree: result?.steps ?? [] }
    });
  } catch (error) {
    shared.webviewPanel?.webview.postMessage({
      type: 'from_extension:full_proof_tree',
      data: { error: getErrorMessage(error) }
    });
  }
};

export default sendFullProofTree;
