import * as vscode from "vscode";
import { Shared } from "../types";
import toggleWebviewPanel from "../actions/toggleWebviewPanel";
import sendPosition from "../actions/sendPosition";

const updateSettingsFromWebview = async (message: any) => {
  if (message.type === 'from_webview:update_settings') {
    const config = vscode.workspace.getConfiguration();
    Object.entries(message.data).forEach(([settingKey, settingValue]) => {
      // ___Does it update User Settings or Workspace Settings?
      //    User Settings.
      //    Argument `vscode.ConfigurationTarget.Global` makes it so that we update User Settings. If we left it out, Workspace Settings would be affected.
      config.update(`paperproof.${settingKey}`, settingValue, vscode.ConfigurationTarget.Global);
    });
  }
}

// NOTE: this gets fired even when we update the settings from the webview (so, even after the function above runs)
const updateSettingsFromExtension = (event: vscode.ConfigurationChangeEvent, shared: Shared) => {
  if (event.affectsConfiguration("paperproof.environment")) {
    // This makes the asset urls reload automatically, without any participation from the developer
    if (shared.webviewPanel) { shared.webviewPanel.dispose(); }
    toggleWebviewPanel(shared);
  }

  if (event.affectsConfiguration("paperproof.isSingleTacticMode")) {
    if (vscode.window.visibleTextEditors[0]) {
      sendPosition(shared, vscode.window.visibleTextEditors[0], (new vscode.CancellationTokenSource()).token);
    }
  }

  if (shared.webviewPanel && event.affectsConfiguration('paperproof')) {
    const config = vscode.workspace.getConfiguration('paperproof');
    const settings = {
      isSingleTacticMode: config.get('isSingleTacticMode'),
      isCompactMode     : config.get('isCompactMode'),
      isCompactTactics  : config.get('isCompactTactics'),
      isHiddenGoalNames : config.get('isHiddenGoalNames'),
      isGreenHypotheses : config.get('isGreenHypotheses'),
      areHypsHighlighted: config.get('areHypsHighlighted'),
    };
    shared.webviewPanel.webview.postMessage({
      type: 'from_extension:update_settings',
      data: settings
    });
  }
}

const getSettings = () => {
  const config = vscode.workspace.getConfiguration('paperproof');
  return {
    isSingleTacticMode: config.get('isSingleTacticMode'),
    isCompactMode     : config.get('isCompactMode'),
    isCompactTactics  : config.get('isCompactTactics'),
    isHiddenGoalNames : config.get('isHiddenGoalNames'),
    isGreenHypotheses : config.get('isGreenHypotheses'),
    areHypsHighlighted: config.get('areHypsHighlighted'),
  };
}

export default {
  updateSettingsFromWebview,
  updateSettingsFromExtension,
  getSettings
};
