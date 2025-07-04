import React from "react";
import { ErroryProofResponse } from "types";

const handleExtensionErrors = (
  proofResponse : ErroryProofResponse,
  setSnackbarMessage: React.Dispatch<React.SetStateAction<String | React.ReactNode>>,
  setSnackbarOpen    : React.Dispatch<React.SetStateAction<boolean>>
) => {
  if (proofResponse.error === 'File changed.' || proofResponse.error === 'stillTyping') {
    // This is a normal situation, just return.
  } else if (proofResponse.error.startsWith('wrongLeanExtensionVersion')) {
    const errorMessage = proofResponse.error.split('wrongLeanExtensionVersion: ')[1];
    setSnackbarMessage(errorMessage);
    setSnackbarOpen(true);
  } else if (proofResponse.error === 'leanNotYetRunning') {
    setSnackbarMessage("Waiting for Lean");
    setSnackbarOpen(true);
  } else if (proofResponse.error.startsWith("No RPC method")) {
    setSnackbarMessage(`Missing "import Paperproof" in this .lean file, please import it.`);
    setSnackbarOpen(true);
  } else if (proofResponse.error === 'zeroProofSteps') {
    setSnackbarMessage("Not within theorem");
    setSnackbarOpen(true);
  } else if (proofResponse.error.startsWith('no snapshot found at')) {
    setSnackbarMessage(<>No snapshot found.<br/>Is your cursor located after <span className="inline-code">#exit</span>?</>);
    setSnackbarOpen(true);
  } else {
    console.warn("We are not handling some error explicitly?", proofResponse);
  }
}

export const versionErrorEl = (desiredVersion: number, leanRpcVersion: number) : React.ReactNode => <>
  Your <b>Paperproof vscode extension</b> has version {desiredVersion}, and <br/>
  your <b>Paperproof Lean library</b> has version {leanRpcVersion}.<br/><br/>
  For Paperproof to work well, these versions must match.
  <br/>
  Please run <span className="inline-code">lake update Paperproof</span> to upgrade the <b>Paperproof Lean library</b> - this is guaranteed to give you matching versions.
  <br/><br/>

  <i className="explanation">Explanation: these version numbers are independent from the paperproof vscode extension version numbers. We update these versions rather rarely, only when we update the response from our lean library in a manner incompatible with the way our vscode extension handles it.</i>
</>

export default handleExtensionErrors;
