import * as vscode from "vscode";

function showNotification(serverUrl : string, sessionId: string) {
  const url = `${serverUrl}/${sessionId}`;
  const openButton: vscode.MessageItem = { title: "Open in browser" };
  vscode.window
    .showInformationMessage(`Your session is available at ${url}`, openButton)
    .then((selectedItem) => {
      if (selectedItem === openButton) {
        vscode.env.openExternal(vscode.Uri.parse(url));
      }
    });
}

function setupStatusBar(serverUrl : string, sessionId: string): vscode.Disposable {
  const statusBarItem = vscode.window.createStatusBarItem(
    vscode.StatusBarAlignment.Right
  );
  statusBarItem.text = "Paperproof";
  statusBarItem.command = "paperproof.showinfo";
  statusBarItem.show();
  const disposable = vscode.commands.registerCommand(
    "paperproof.showinfo",
    () => {
      showNotification(serverUrl, sessionId);
    }
  );
  showNotification(serverUrl, sessionId);
  return disposable;
}

export default setupStatusBar;
