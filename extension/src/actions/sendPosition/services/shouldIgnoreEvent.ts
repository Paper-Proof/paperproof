import * as vscode from "vscode";

const shouldIgnoreEvent = (editor: vscode.TextEditor) : Boolean => {
  // Apparently lean4 documents sometimes have language id "lean"
  // (https://github.com/leanprover/vscode-lean4/blob/02a6d4917f658bc1ee98933a809c0369e9827a0d/vscode-lean4/src/utils/clientProvider.ts#L175C46-L175C46)
  if (editor.document.languageId !== "lean4" && editor.document.languageId !== "lean") {
    return true;
  }
  // We should ignore it when the user is selecting a range of text
  if (!editor.selection.isEmpty) {
    return true;
  }
  return false;
};

export default shouldIgnoreEvent;
