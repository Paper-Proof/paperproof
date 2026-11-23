import React from "react";
import { createRoot } from "react-dom/client";
import { Paperproof } from "../embed/dist/react.js";

declare const window: Window & { PAPERPROOF_PROOF: unknown };

createRoot(document.getElementById("root")!).render(<Paperproof proof={window.PAPERPROOF_PROOF}/>);
