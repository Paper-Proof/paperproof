import * as React from "react";
import { useContext, useEffect, useState } from "react";
import { EditorContext, RpcContext, useAsync } from "@leanprover/infoview";
import { Location } from "vscode-languageserver-protocol";
import App from "./tldraw_stuff/App.tsx";
import * as ReactDOM from "react-dom";

// I think indexVscode.tsx should always send the infoTree to localhost:3000, mb based on option later, no need to create 2 files.

// So, we have 2 entries - indexIpad and indexVscode.
// They are bundled differently - browser needs "iife" code (bc), and 
// [TODO] actually - maybe vscode *will* understand our bundled paperProof.js code! Let's try it.
// [TODO] also actually - maybe browser will understand my script tag now!
export default function () {
  const editorConnection = useContext(EditorContext);
  const rs = useContext(RpcContext);
  const [location, setLocation] = useState<Location | undefined>(undefined);

  useEffect(() => {
    return editorConnection.events.changedCursorLocation.on((loc) => {
      setLocation(loc);
    }).dispose;
  }, [rs]);

  const response = useAsync<any>(async () => {
    if (!location) {
      return Promise.reject();
    }
    const context = await rs.call("getPpContext", {
      pos: location.range.start,
    });

    // Later we'll add an option of whether to send this.
    try {
      await fetch("http://localhost:3000/sendTypes", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: context as string,
      });
    } catch (e) {
      console.log("ERROR FROM POST", e);
    }

    return context;
  }, [location]);

  if (response.state === "loading") {
    return <div>Loading...</div>;
  } else if (response.state === "rejected") {
    return <div>Error: {anyToString(response.error)}</div>;
  } else {
    return <section>
      <h1>Tsss</h1>
      <App proofTree={JSON.parse(response.value)}/>
    </section>;
  }
}

function anyToString(s: any): string {
  if (typeof s === "string") {
    return s;
  }
  return JSON.stringify(s);
}
