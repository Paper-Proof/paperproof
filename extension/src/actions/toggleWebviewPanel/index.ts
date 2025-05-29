import * as vscode from "vscode";
import { Shared } from "../../types";
import getWebviewContent from './services/getWebviewContent';

const toggleWebviewPanel = (shared: Shared) => {
  if (shared.webviewPanel) {
    shared.webviewPanel.dispose();
  } else {
    const webviewPanel = vscode.window.createWebviewPanel(
      "paperproof",
      "Paperproof",
      { viewColumn: vscode.ViewColumn.Two, preserveFocus: true },
      { enableScripts: true, retainContextWhenHidden: true }
    );
    webviewPanel.webview.html = getWebviewContent(shared, webviewPanel);

    // Handle settings updates from webview
    webviewPanel.webview.onDidReceiveMessage(async (message) => {
      if (message.type === 'from_webview:update_settings') {
        const config = vscode.workspace.getConfiguration();
        Object.entries(message.data).forEach(([settingKey, settingValue]) => {
          // ___Does it update User Settings or Workspace Settings?
          //    User Settings.
          //    Argument `vscode.ConfigurationTarget.Global` makes it so that we update User Settings. If we left it out, Workspace Settings would be affected.
          config.update(`paperproof.${settingKey}`, settingValue, vscode.ConfigurationTarget.Global);
        });
      }
    });

    // Listen for VSCode settings changes and notify webview
    const configurationListener = vscode.workspace.onDidChangeConfiguration((event) => {
      if (event.affectsConfiguration('paperproof')) {
        const config = vscode.workspace.getConfiguration('paperproof');
        webviewPanel.webview.postMessage({
          type: 'from_extension:update_settings',
          data: {
            isCompactMode    : config.get('isCompactMode'),
            isCompactTactics : config.get('isCompactTactics'),
            isReadonlyMode   : config.get('isReadonlyMode'),
            isHiddenGoalNames: config.get('isHiddenGoalNames'),
            isGreenHypotheses: config.get('isGreenHypotheses')
          }
        });
      }
    });

    // Clean up the configuration listener when webview is closed
    webviewPanel.onDidDispose(() => { 
      shared.webviewPanel = null;
      configurationListener.dispose();
    });
    
    shared.webviewPanel = webviewPanel;
  }
};

export default toggleWebviewPanel;
