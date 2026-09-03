import * as vscode from "vscode";
import { TextDocumentPositionParams } from "vscode-languageserver-protocol";
import { ProofState, Shared } from "../../../types";
import { getShadowDoc } from "../../../services/noInstall/shadowDoc";

// Paperproof is serverless: the parser is injected into a hidden shadow document,
// so no `require paperproof` in the lakefile is needed. Both the tree and the goal
// come from that shadow - asking the real file for goals would hand us ids from a
// different elaboration, which nothing in the tree could match.
const fetchLeanData = async (
  shared: Shared,
  client: any,
  editor: vscode.TextEditor,
  tdp: TextDocumentPositionParams
): Promise<ProofState> => {
  const singleTactic = !!vscode.workspace.getConfiguration("paperproof").get("isSingleTacticMode");

  const shadow = getShadowDoc(shared.context, shared.log, client, editor.document);
  if (!shadow) {
    throw new Error("noLeanProject");
  }
  const result = await shadow.query(editor.selection.active, singleTactic);

  return { goal: result?.goal ?? null, proofTree: result?.steps ?? [] };
};

export default fetchLeanData;
