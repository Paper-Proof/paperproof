import * as React from "react";
import { track, useDefaultHelpers } from "@tldraw/tldraw";
import { ProofResponse } from "types";

const ErrorToast = track(() => {
  const { addToast, clearToasts } = useDefaultHelpers()

  React.useEffect(() => {
    addEventListener("message", (event) => {
      const proof: ProofResponse = event.data;
      if (!proof || !("error" in proof)) {
        clearToasts();
        return;
      }

      console.log(proof);

      clearToasts();
      if (proof.error === 'File changed.' || proof.error === 'stillTyping') {
        addToast({ title: "Still typing" });
        return;
      } else if (proof.error === 'leanNotYetRunning') {
        addToast({ title: "Waiting for Lean" });
      } else if (proof.error.startsWith("No RPC method")) {
        addToast({
          title: "Please import <b>paperproof</b>",
          description: "In order to use <b>paperpoof</b>, you need to 1. install a paperproof lean library <br/>2. import it from your file"
        })
      } else if (proof.error === 'zeroProofSteps') {
        addToast({
          title: "Not within theorem"
        })
      }
    });
  })

  return null
})

export default ErrorToast
