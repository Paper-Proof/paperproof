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
  } else if (proofResponse.error === 'leanExtensionNotFound') {
    setSnackbarMessage(<>Paperproof needs the <b>lean4</b> vscode extension - please install it.</>);
    setSnackbarOpen(true);
  } else if (proofResponse.error === 'leanNotYetRunning' || proofResponse.error === 'leanClientNotFound') {
    setSnackbarMessage("Waiting for Lean");
    setSnackbarOpen(true);
  } else if (proofResponse.error === 'noLeanProject') {
    setSnackbarMessage(<>No <span className="inline-code">lean-toolchain</span> above this file.<br/>Please open a Lean project.</>);
    setSnackbarOpen(true);
  } else if (proofResponse.error === 'noParserForLeanVersion') {
    setSnackbarMessage(<>
      Paperproof doesn't have a parser for Lean {proofResponse.meta?.leanVersion ? <> (<b>v{proofResponse.meta.leanVersion}</b>)</> : ''} yet.<br/>
      Please <a href="https://github.com/Paper-Proof/paperproof/issues/new" target="_blank" rel="noopener noreferrer">open an issue</a> - Lean updates its metaprogramming api often, and it helps to hear about it early.
    </>);
    setSnackbarOpen(true);
  } else if (proofResponse.error === 'zeroProofSteps') {
    setSnackbarMessage("Not within theorem");
    setSnackbarOpen(true);
  } else {
    console.warn("We are not handling some error explicitly?", proofResponse);
  }
}

export default handleExtensionErrors;
