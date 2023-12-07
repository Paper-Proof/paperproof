import * as vscode from 'vscode';
import { ProofStateOrError, Shared } from "../../../types";

function getWebviewContent(shared: Shared, webviewPanel: vscode.WebviewPanel, serverUrl: string, initialInfo: ProofStateOrError, isBrightTheme: boolean) {
  // [For paperproof:offline]
  // const pathJs = vscode.Uri.joinPath(shared.context.extensionUri, 'dist', 'indexBrowser.js');
  // const webviewPathJs = webviewPanel.webview.asWebviewUri(pathJs);
  // const pathCss = vscode.Uri.joinPath(shared.context.extensionUri, 'dist', 'indexBrowser.css');
  // const webviewPathCss = webviewPanel.webview.asWebviewUri(pathCss);

  return `
  <!DOCTYPE html>
  <html lang="en">
    <head>
      <meta charset="UTF-8">
      <meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover"/>
      <link href="${serverUrl}/indexBrowser.css" rel="stylesheet">
      <title>Paperproof</title>
    </head>
    <body>
      <script>
        window.initialInfo = ${JSON.stringify(initialInfo)};
        window.isBrightTheme = ${isBrightTheme};
      </script>
      <div id="root"></div>
      <script src="${serverUrl}/indexBrowser.js"></script>
    </body>
  </html>`;
}

export default getWebviewContent;
