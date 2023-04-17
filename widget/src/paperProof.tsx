import * as React from "react";
import { useContext, useEffect, useState } from "react";
import { EditorContext, RpcContext, useAsync } from "@leanprover/infoview";
import { Location } from "vscode-languageserver-protocol";

import App from "./tldraw_stuff/App.tsx";


export default function () {
  // const editorConnection = useContext(EditorContext);
  // const rs = useContext(RpcContext);
  // const [location, setLocation] = useState<Location | undefined>(undefined);

  // useEffect(() => {
  //   return editorConnection.events.changedCursorLocation.on((loc) => {
  //     setLocation(loc);
  //   }).dispose;
  // }, [rs]);

  // const response = useAsync<any>(async () => {
  //   if (!location) {
  //     return Promise.reject();
  //   }
  //   const context = await rs.call("getPpContext", {
  //     pos: location.range.start,
  //   });
  //   try {
  //     await fetch("http://localhost:3000/sendTypes", {
  //       method: "POST",
  //       headers: { "Content-Type": "application/json" },
  //       body: context as string,
  //     });
  //   } catch (e) {
  //     console.log("ERROR FROM POST", e);
  //   }

  //   return context;
  // }, [location]);

  // if (response.state === "loading") {
  //   return <div>loading...</div>;
  // }

  // if (response.state === "rejected") {
  //   return <div>Error: {anyToString(response.error)}</div>;
  // }

  // return <div>{response.value}</div>;

  // return <App/>;
  return <App/>;

}




function anyToString(s: any): string {
  if (typeof s === "string") {
    return s;
  }
  return JSON.stringify(s);
}
