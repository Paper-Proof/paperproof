import * as vscode from 'vscode';
import { Shared } from "../../../types";
import Settings from '../../../services/Settings';

function getWebviewContent(shared: Shared, webviewPanel: vscode.WebviewPanel) {
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
        window.initialSettings = ${JSON.stringify(Settings.getSettings())};
      </script>
      <div id="root"></div>
      <script src="${js}"></script>
    </body>
  </html>`;
}

export default getWebviewContent;
