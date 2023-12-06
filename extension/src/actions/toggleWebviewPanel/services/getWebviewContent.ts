import { ProofStateOrError } from "../../../types";

function getWebviewContent(serverUrl: string, initialInfo: ProofStateOrError, isBrightTheme: boolean) {
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
