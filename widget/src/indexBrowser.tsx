import * as React from "react";
import { useEffect } from "react";
import * as ReactDOM from "react-dom";
import { Tldraw } from "@tldraw/tldraw";
import "@tldraw/tldraw/editor.css";
import "@tldraw/tldraw/ui.css";

let lastId = 0;

function App() {
  useEffect(() => {
    function getTypes() {
      fetch("getTypes")
        .then((response) => response.json())
        .then((res) => {
          const proofTree = res.data;
          const id = Number(res.id);
          if (id > lastId) {
            console.log(id, proofTree);
            lastId = id;
          }
        })
        .catch((e) => {
          console.log("error", e);
        });
    }
    const interval = setInterval(getTypes, 200);
    return () => clearInterval(interval);
  }, []);
  return (
    <div
      style={{
        position: "fixed",
        inset: 0,
      }}
    >
      <Tldraw />
    </div>
  );
}

ReactDOM.render(
  <React.StrictMode>
    <App />
  </React.StrictMode>,
  document.getElementById("root")
);
