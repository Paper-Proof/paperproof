import * as React from "react";
import { useContext, useEffect, useState } from "react";
import { EditorContext, RpcContext, useAsync } from "@leanprover/infoview";
import {
  TextDocumentPositionParams,
  Location,
} from "vscode-languageserver-protocol";

export default function () {
  const editorConnection = useContext(EditorContext);
  const rs = useContext(RpcContext);
  const [location, setLocation] = useState<Location | undefined>(undefined);

  useEffect(() => {
    return editorConnection.events.changedCursorLocation.on((loc) => {
      setLocation(loc);
    }).dispose;
  }, [rs]);

  const response = useAsync(async () => {
    if (!location) {
      return Promise.reject();
    }
    const arg: TextDocumentPositionParams = {
      textDocument: {
        uri: location.uri,
      },
      position: location.range.start,
    };
    return rs.call("Lean.Widget.getInteractiveTermGoal", arg);
  }, [location]);

  return (
    <div>
      {response.state === "loading"
        ? "loading..."
        : response.state === "rejected"
        ? JSON.stringify(response.error)
        : JSON.stringify(response.value)}
    </div>
  );
}
