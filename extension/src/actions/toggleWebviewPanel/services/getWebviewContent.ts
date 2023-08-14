import { ProofState, ProofError } from "../../../types";

function getWebviewContent(serverUrl : string, initialInfo: ProofState | ProofError | null) {
  return `
  <!DOCTYPE html>
  <html lang="en">
    <head>
      <meta charset="UTF-8">
      <meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover"/>
      <title>Paperproof</title>
    </head>
    <body>
      <script>initialInfo = ${JSON.stringify(initialInfo)}</script>
      <div id="root"></div>
      <script src="${serverUrl}/indexBrowser.js"></script>
    </body>
  </html>`;
}

export default getWebviewContent;
