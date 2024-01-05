import * as vscode from 'vscode';
import { ProofStateOrError, Shared } from "../../../types";

function getWebviewContent(shared: Shared, webviewPanel: vscode.WebviewPanel, initialInfo: ProofStateOrError) {
  let js = "";
  let css = "";
  const environment = vscode.workspace.getConfiguration("paperproof").get("environment");
  if (environment === "production") {
    const pathJs = vscode.Uri.joinPath(shared.context.extensionUri, 'dist', 'indexBrowser.js');
    js = webviewPanel.webview.asWebviewUri(pathJs).toString();
    const pathCss = vscode.Uri.joinPath(shared.context.extensionUri, 'dist', 'indexBrowser.css');
    css = webviewPanel.webview.asWebviewUri(pathCss).toString();
  } else if (environment === "development") {
    js = "http://localhost:80/indexBrowser.js";
    css = "http://localhost:80/indexBrowser.css";
  }

  return `
  <!DOCTYPE html>
  <html lang="en">
    <head>
      <meta charset="UTF-8">
      <meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover"/>
      <link href="${css}" rel="stylesheet">
      <title>Paperproof</title>
    </head>
    <body>
      <script>
        window.initialInfo = ${JSON.stringify(initialInfo)};
      </script>
      <div id="root"></div>
      <script src="${js}"></script>
    </body>
  </html>`;
}

export default getWebviewContent;
