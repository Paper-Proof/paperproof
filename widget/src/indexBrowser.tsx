import * as React from "react";
import * as ReactDOM from "react-dom";
import { Tldraw } from "@tldraw/tldraw";
import "@tldraw/tldraw/editor.css";
import "@tldraw/tldraw/ui.css";

ReactDOM.render(
  <React.StrictMode>
    <div
      style={{
        position: "fixed",
        inset: 0,
      }}
    >
      <Tldraw />
    </div>
  </React.StrictMode>,
  document.getElementById("root")
);
