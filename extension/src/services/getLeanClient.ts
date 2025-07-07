import * as vscode from "vscode";
import getErrorMessage from "./getErrorMessage";
import { Shared } from "../types";

const getLeanClient = async (shared: Shared) => {
  const leanExtension = vscode.extensions.getExtension("leanprover.lean4");
  if (!leanExtension) {
    throw new Error("leanExtensionNotFound");
  }

  let client;
  try {
    // v0.0.144 (and some other versions)
    if (leanExtension.exports.clientProvider) {
      const clientProvider = leanExtension.exports.clientProvider;
      client = clientProvider.getActiveClient();
    // v0.0.176 (and some other versions)
    } else {
      const clientProvider = (await leanExtension.exports.lean4EnabledFeatures).clientProvider;
      client = clientProvider.getActiveClient();
    }
  } catch (error) {
    shared.log.appendLine(getErrorMessage(error));

    const version = leanExtension.packageJSON.version;
    const errorMessage = `
      Please press <span class="inline-code">CMD+SHIFT+P</span>, type <span class="command-name">"Extensions: Install Specific Version of Extension..."</span>, and change your <b>lean4 vscode extension</b> to one of these versions: <b>v0.0.176</b>, <b>v0.0.144</b>.<br/>
      Your <b>lean4 vscode extension</b> version is currently: <b>v${version}</b>.
      <br/><br/>

      <i class="explanation">Explanation: Paperproof depends on lean4 extension in order to avoid loading your computer with excessive Lean server instances; however lean4 api regularly updates in a way that introduces breaking changes, resulting in a blank screen in Paperproof. Hopefully their api stabilizes soon and we can remove this step, but at the moment - please downgrade the lean4 extension, and turn off automatic extension updates for lean4.</i>
    `;
    throw new Error(`wrongLeanExtensionVersion: ${errorMessage}`);
  }

  if (!client) {
    throw new Error("leanClientNotFound");
  }

  if (!client.running) {
    // TODO this is desired, but temporarily disabled to debug asynchronicity
    // NOTE it looks like it works nicely without this too? Is this only useful on vscode editor startup?
    //
    // Dispose of the previous listener if there was one
    // shared.onLeanClientRestarted?.dispose();
    // shared.onLeanClientRestarted = client.restarted(() => {
    //   sendPosition(shared, editor)
    //   .then(() => {
    //     shared.onLeanClientRestarted?.dispose();
    //   });
    // });
    throw new Error("leanNotYetRunning");
  }

  return client;
};

export default getLeanClient;
