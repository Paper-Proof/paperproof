import * as vscode from "vscode";
import { TextDocumentPositionParams } from "vscode-languageserver-protocol";

// Simple request. We don't keep session open and create a new one for each request for now.
const vscodeRequest = async (log: vscode.OutputChannel, method: string, client: any, uri: string, tdp: TextDocumentPositionParams, params: any): Promise<any> => {
  log.appendLine(`Making ${method} request`);
  const connection = await client.sendRequest("$/lean/rpc/connect", { uri });
  const response = await client.sendRequest("$/lean/rpc/call", {
    sessionId: connection.sessionId,
    method,
    // These are always needed for Lean rpcs
    // (https://github.com/leanprover/lean4/blob/367b38701fb9cca80328624a016c3b3acfd5e2cd/src/Lean/Data/Lsp/Basic.lean#L288)
    ...tdp,
    params,
  });
  return response;
};

export default vscodeRequest;
