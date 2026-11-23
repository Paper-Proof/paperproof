import React from "react";
import { createRoot, Root } from "react-dom/client";
import type { PaperproofFit } from "../react";
import PaperproofView, { PaperproofViewProps } from "./components/PaperproofView";
import "@app/index.css";
import "@app/css/theorem.css";
import "./paperproof.css";
import CSS from "pp:css";

export type ShadowTreeProps = Omit<PaperproofViewProps, "onLayout" | "onState"> & { fit?: PaperproofFit };

let sheet: CSSStyleSheet | null = null;
const styleSheet = () => {
  if (!sheet) { sheet = new CSSStyleSheet(); sheet.replaceSync(CSS); }
  return sheet;
};

const FIT_STEP = 4;

export class ShadowTree {
  #host: HTMLElement;
  #container = document.createElement("div");
  #fitStyle = document.createElement("style");
  #root: Root;
  #props: ShadowTreeProps | null = null;
  #isUnmounted = false;
  #naturalWidth = 0;
  #resizeObserver = new ResizeObserver(() => this.#fit());

  constructor(host: HTMLElement) {
    this.#host = host;
    const shadow = host.shadowRoot ?? host.attachShadow({ mode: "open" });
    shadow.adoptedStyleSheets = [styleSheet()];
    shadow.replaceChildren(this.#fitStyle, this.#container);
    this.#root = createRoot(this.#container);
  }

  render(props: ShadowTreeProps) {
    this.#props = props;
    this.#draw();
  }

  unmount() {
    this.#isUnmounted = true;
    this.#resizeObserver.disconnect();
    const root = this.#root;
    queueMicrotask(() => root.unmount());
  }

  #draw() {
    if (this.#isUnmounted || !this.#props) return;
    const { fit = "scale", ...props } = this.#props;
    this.#container.className = `pp-host -fit-${fit}`;
    this.#naturalWidth = 0;
    this.#root.render(
      <PaperproofView
        {...props}
        onLayout={() => this.#fit()}
        onState={(state) => this.#host.setAttribute("data-state", state)}
      />
    );
  }

  #fit() {
    const wrap = this.#container.querySelector(".pp-wrap");
    if (!wrap) return;
    this.#resizeObserver.observe(wrap);
    this.#container.classList.add("-measuring");
    const width = Math.ceil(wrap.getBoundingClientRect().width);
    this.#container.classList.remove("-measuring");
    this.#host.setAttribute("data-width", String(Math.ceil(wrap.getBoundingClientRect().width)));
    this.#host.setAttribute("data-height", String(Math.ceil(this.#host.getBoundingClientRect().height)));
    if (width === this.#naturalWidth) return;
    this.#naturalWidth = width;
    let css = "";
    if (this.#props?.fit !== "scroll" && this.#props?.fit !== "none") {
      for (let column = width - 1; column > width / 4; column -= FIT_STEP) {
        css += `@container (max-width: ${column}px) { .proof-tree { zoom: ${((column - FIT_STEP) / width).toFixed(4)}; } }\n`;
      }
    }
    this.#fitStyle.textContent = css;
  }
}
