import * as React from "react";
import { useContext, useEffect, useState } from "react";
import { EditorContext, RpcContext, useAsync } from "@leanprover/infoview";
import {
  TextDocumentPositionParams,
  Location,
} from "vscode-languageserver-protocol";
import { toGoodFormat, transform } from "./prettyPrint";

export default function () {
  const editorConnection = useContext(EditorContext);
  const rs = useContext(RpcContext);
  const [location, setLocation] = useState<Location | undefined>(undefined);

  useEffect(() => {
    return editorConnection.events.changedCursorLocation.on((loc) => {
      setLocation(loc);
    }).dispose;
  }, [rs]);

  const response = useAsync<any[]>(async () => {
    if (!location) {
      return Promise.reject();
    }
    const arg: TextDocumentPositionParams = {
      textDocument: {
        uri: location.uri,
      },
      position: location.range.start,
    };
    // Use zod instead of as any
    const result = (await rs.call(
      "Lean.Widget.getInteractiveGoals",
      arg
    )) as any;
    return (result.goals.length > 0 ? result.goals[0].hyps ?? [] : []).map(
      (h: any) => {
        const type = h.type ? toGoodFormat(transform(h.type)) : [];
        return `${h.names.join(",")}: ${type.join()}`;
      }
    );
  }, [location]);

  if (response.state === "loading") {
    return <div>loading...</div>;
  }

  if (response.state === "rejected") {
    return <div>{JSON.stringify(response.error)}</div>;
  }

  return (
    <div>
      Hello world!
      {response.value.map((v) => (
        <div>{v}</div>
      ))}
    </div>
  );
}
