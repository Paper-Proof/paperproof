import * as vscode from "vscode";
import { TextDocumentPositionParams } from "vscode-languageserver-protocol";
import { ProofState } from "../../../types";
import vscodeRequest from "../../../services/vscodeRequest";

const fetchLeanData = async (log: vscode.OutputChannel, client: any, tdp: TextDocumentPositionParams) : Promise<ProofState> => {
  const uri = tdp.textDocument.uri;
  const proofTreeResponse = await vscodeRequest(log, "getSnapshotData", client, uri, tdp, { pos: tdp.position });
  const goalsResponse = await vscodeRequest(log, "Lean.Widget.getInteractiveGoals", client, uri, tdp, tdp);

  return {
    goal: (goalsResponse && goalsResponse.goals[0]) || null,
    proofTree: proofTreeResponse.steps,
    version: proofTreeResponse.version ?? undefined,
  };
};

export default fetchLeanData;
