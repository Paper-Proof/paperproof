import * as React from "react";
import { EditorContext } from "@leanprover/infoview";

export default function () {
  const editorConnection = React.useContext(EditorContext);

  function onClick() {
    editorConnection.api.insertText("-- Check widget wiring", "above");
  }

  return (
    <div>
      <button onClick={onClick}>insert</button>
    </div>
  );
}
