import * as React from "react";
import { track, useDefaultHelpers } from "@tldraw/tldraw";
import { ProofResponse } from "types";

const ErrorToast = track(() => {
  const { addToast, clearToasts } = useDefaultHelpers()

  React.useEffect(() => {
    addEventListener("message", (event) => {
      clearToasts();

      const proof: ProofResponse = event.data;

      if (!proof || !("error" in proof)) {
        return;
      }

      if (proof.error === 'File changed.' || proof.error === 'stillTyping') {
        return;
      } else if (proof.error === 'leanNotYetRunning') {
        addToast({
          title: "Waiting for Lean",
          keepOpen: true
        });
      } else if (proof.error.startsWith("No RPC method")) {
        addToast({
          title: 'Missing "import Paperproof" in this file',
          description: 'Please import a Paperproof Lean library in this file.',
          keepOpen: true
        });
      } else if (proof.error === 'zeroProofSteps') {
        addToast({
          title: "Not within theorem",
          keepOpen: true
        });
      }
    });
  })

  return null
})

export default ErrorToast
