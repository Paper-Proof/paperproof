import * as vscode from "vscode";
import { TextDocumentPositionParams } from "vscode-languageserver-protocol";
import { ProofState, Shared } from "../../../types";
import vscodeRequest from "../../../services/vscodeRequest";

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

  // Save for later sending in case there is no session for the server or no webview open yet.
  shared.latestInfo = body;
  // Send directly to the webview (if it's open!) to avoid lag
  await webviewPanel?.webview.postMessage(body);

  log.appendLine("🎉 Sent everything");
};

export default sendInfoAtTdp;
