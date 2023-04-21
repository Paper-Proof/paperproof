import * as React from "react";
import { useContext, useEffect, useState } from "react";
import { EditorContext, RpcContext, useAsync } from "@leanprover/infoview";
import { Location } from "vscode-languageserver-protocol";

export default function () {
  const editorConnection = useContext(EditorContext);
  const rs = useContext(RpcContext);
  const [location, setLocation] = useState<Location | undefined>(undefined);
  const [serverError, setServerError] = useState(null);

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

    setServerError(null);
    await fetch("http://localhost:3000/sendTypes", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: context as string,
    }).catch((error) => {
      setServerError(serverError);
    });

    return context;
  }, [location]);

  if (serverError) {
    return <div>Server error: {anyToString(serverError)}</div>;
  }

  if (response.state === "loading") {
    return <div>Loading...</div>;
  } else if (response.state === "rejected") {
    return <div>Error: {anyToString(response.error)}</div>;
  } else {
    return (
      <section>
        <h2>Just sent this InfoTree to the node server:</h2>
        <pre>
          <code>{response.value}</code>
        </pre>
      </section>
    );
  }
}

function anyToString(s: any): string {
  if (typeof s === "string") {
    return s;
  }
  return JSON.stringify(s);
}
