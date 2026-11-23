import React, { useLayoutEffect, useState } from "react";
import { createRoot, Root } from "react-dom/client";
import { ConvertedProofTree, DEFAULT_LATEX_SETTINGS, Highlights, LatexSettings, NaturalProofTree, Settings, SNAPSHOT_VERSION, SnapshotPayload } from "types";
import hypsToTables from "@app/services/hypsToTables";
import naturalToConverted from "@app/services/naturalToConverted";
import { collectTexts } from "@app/services/convertToLatex";
import { validate, formatProblems, Problem } from "@app/format";
import ProofTreeView, { DEFAULT_SETTINGS } from "./ProofTreeView";
import ProofTreeErrorBoundary from "./ProofTreeErrorBoundary";
import "@app/index.css";
import "@app/css/theorem.css";
import "./embed.css";
import CSS from "pp:css";

declare const PP_VERSION: string;
declare const KATEX_VERSION: string;

declare global {
  interface Window { Paperproof?: { version: string; validate: typeof validate } }
}

const THEMES = ["sand", "cyan", "check", "square", "check-goal", "slate", "clay"] as const;
type Theme = typeof THEMES[number];
const isTheme = (x: unknown): x is Theme => THEMES.includes(x as Theme);
const THEME_LABELS: Record<Theme, string> = {
  sand: "Sand", cyan: "Cyan, with 🎉", check: "Green ✓", square: "■ after the text",
  "check-goal": "✓ on the goal", slate: "Slate", clay: "Clay",
};

const THEME_KEY = "paperproof-theme";
const DARK_BARS_KEY = "paperproof-dark-bars";
const stored = (key: string) => { try { return localStorage.getItem(key); } catch { return null; } };
const store = (key: string, value: string) => { try { localStorage.setItem(key, value); } catch { /* blocked: this page only */ } };

const KATEX = `https://cdn.jsdelivr.net/npm/katex@${KATEX_VERSION}/dist/katex.min`;
let katexLoading: Promise<void> | null = null;
const loadKatex = () => katexLoading ??= new Promise<void>((resolve) => {
  const link = document.createElement("link");
  link.rel = "stylesheet";
  link.href = `${KATEX}.css`;
  document.head.appendChild(link);
  const script = document.createElement("script");
  script.src = `${KATEX}.js`;
  script.onload = script.onerror = () => resolve();
  document.head.appendChild(script);
});

let sheet: CSSStyleSheet | null = null;
const styleSheet = () => {
  if (!sheet) { sheet = new CSSStyleSheet(); sheet.replaceSync(CSS); }
  return sheet;
};

const FIT_STEP = 4;

interface View {
  tree: ConvertedProofTree;
  settings: Settings;
  highlights: Highlights;
  collapsedBoxIds: string[];
  deletedHypothesisNames: string[];
  latexSettings: LatexSettings;
}

const latexSettingsFor = (tree: ConvertedProofTree): LatexSettings => {
  const { stable, changing } = collectTexts(tree);
  const map: Record<string, string> = {};
  for (const text of [...stable, ...changing]) map[text] = text;
  return { ...DEFAULT_LATEX_SETTINGS, isActive: true, map };
};

const viewOfNatural = (natural: NaturalProofTree, settings: Settings): View => {
  const tree = naturalToConverted(natural);
  tree.boxes.forEach((box) => { box.hypTables = hypsToTables(box.hypLayers, tree, false); });
  return {
    tree, settings, highlights: null, collapsedBoxIds: [], deletedHypothesisNames: [],
    latexSettings: natural.format === "latex" ? latexSettingsFor(tree) : DEFAULT_LATEX_SETTINGS,
  };
};

const viewOfSnapshot = (payload: SnapshotPayload): View => {
  payload.proofTree.boxes.forEach((box) => {
    box.hypTables = hypsToTables(box.hypLayers, payload.proofTree, payload.settings.isSingleTacticMode);
  });
  return {
    tree: payload.proofTree, settings: payload.settings, highlights: payload.highlights,
    collapsedBoxIds: payload.collapsedBoxIds, deletedHypothesisNames: payload.deletedHypothesisNames,
    latexSettings: payload.latexSettings,
  };
};

const Tree = ({ view, problems, onLayout }: { view: View; problems: Problem[]; onLayout: () => void }) => {
  const [settings, setSettings] = useState(view.settings);
  const [collapsedBoxIds, setCollapsedBoxIds] = useState(view.collapsedBoxIds);
  const [deletedHypothesisNames, setDeletedHypothesisNames] = useState(view.deletedHypothesisNames);
  const [latexSettings, setLatexSettings] = useState(view.latexSettings);
  useLayoutEffect(onLayout);
  return (
    <>
      <div className="pp-wrap">
        <ProofTreeErrorBoundary>
          <ProofTreeView
            proofTree={view.tree}
            highlights={view.highlights}
            settings={settings}                             setSettings={setSettings}
            collapsedBoxIds={collapsedBoxIds}               setCollapsedBoxIds={setCollapsedBoxIds}
            deletedHypothesisNames={deletedHypothesisNames} setDeletedHypothesisNames={setDeletedHypothesisNames}
            latexSettings={latexSettings}                   setLatexSettings={setLatexSettings}
          />
        </ProofTreeErrorBoundary>
      </div>
      {problems.length > 0 && <pre className="pp-problems">{formatProblems(problems)}</pre>}
    </>
  );
};

class PaperproofProofElement extends HTMLElement {
  static observedAttributes = ["theme", "dark-bars", "fit", "font-size", "unlimited-width", "kind"];

  #shadow: ShadowRoot;
  #rootEl: HTMLDivElement;
  #fitStyle: HTMLStyleElement;
  #katexLink: HTMLLinkElement | null = null;
  #root: Root | null = null;
  #proof: unknown = undefined;
  #hasProof = false;
  #renders = 0;
  #naturalWidth = 0;
  #resizeObserver = new ResizeObserver(() => this.#fit());
  #menu: HTMLDivElement | null = null;
  static #mounted = new Set<PaperproofProofElement>();

  static renderAll() {
    PaperproofProofElement.#mounted.forEach((el) => el.#render());
  }

  constructor() {
    super();
    this.#shadow = this.attachShadow({ mode: "open" });
    this.#shadow.adoptedStyleSheets = [styleSheet()];
    this.#fitStyle = document.createElement("style");
    this.#rootEl = document.createElement("div");
    this.#shadow.append(this.#fitStyle, this.#rootEl);
    this.#rootEl.addEventListener("contextmenu", (event) => this.#openMenu(event));
    if (Object.prototype.hasOwnProperty.call(this, "proof")) {
      const proof = (this as { proof?: unknown }).proof;
      delete (this as { proof?: unknown }).proof;
      this.proof = proof;
    }
  }

  get proof() { return this.#proof; }
  set proof(proof: unknown) {
    if (this.#hasProof && JSON.stringify(proof) === JSON.stringify(this.#proof)) return;
    this.#proof = proof;
    this.#hasProof = true;
    if (this.isConnected) this.#render();
  }

  connectedCallback() {
    if (document.readyState === "loading") {
      document.addEventListener("DOMContentLoaded", () => this.#mount(), { once: true });
    } else {
      this.#mount();
    }
  }

  disconnectedCallback() {
    PaperproofProofElement.#mounted.delete(this);
    this.#closeMenu();
    this.#resizeObserver.disconnect();
    this.#root?.unmount();
    this.#root = null;
  }

  attributeChangedCallback() {
    if (this.#root) this.#render();
  }

  async #mount() {
    if (this.#root || !this.isConnected) return;
    this.#root = createRoot(this.#rootEl);
    PaperproofProofElement.#mounted.add(this);
    if (this.#hasProof) return this.#render();
    try {
      const proof = await this.#readProof();
      if (!this.#hasProof) this.proof = proof;
    } catch (e) {
      if (!this.#hasProof) this.#showError(e instanceof Error ? e.message : String(e));
    }
  }

  async #readProof(): Promise<unknown> {
    const src = this.getAttribute("src");
    if (src) {
      const res = await fetch(src);
      if (!res.ok) throw new Error(`could not load ${src}: ${res.status}`);
      return res.json();
    }
    const script = this.querySelector('script[type="application/json"]');
    if (!script) throw new Error('put the proof JSON in a <script type="application/json"> inside <paperproof-proof>, or give it a src');
    return JSON.parse(script.textContent ?? "");
  }

  #showError(message: string) {
    this.setAttribute("data-state", "error");
    this.#root?.render(<pre className="pp-error">Paperproof: {message}</pre>);
  }

  async #render() {
    if (!this.#root) return;
    const themeAttr = this.getAttribute("theme");
    if (themeAttr !== null && !isTheme(themeAttr)) console.warn(`[paperproof] theme="${themeAttr}" is not one of ${THEMES.join(", ")}`);
    const isSnapshot = this.getAttribute("kind") === "snapshot";
    this.#rootEl.className = `pp-root -theme-${this.#theme()} ${isSnapshot ? "-snapshot" : "-natural"} ${this.#darkBars() ? "-dark-bars" : ""}`;

    let view: View;
    let problems: Problem[] = [];
    if (isSnapshot) {
      const payload = this.#proof as SnapshotPayload;
      if (!payload?.proofTree?.boxes) return this.#showError("this snapshot has no proof in it");
      if (payload.version > SNAPSHOT_VERSION) return this.#showError("this snapshot was made by a newer version of Paperproof");
      view = viewOfSnapshot(payload);
    } else {
      const result = validate(this.#proof);
      result.problems.filter((p) => p.level === "warning").forEach((p) => console.warn(`[paperproof] ${p.path}: ${p.message}`));
      problems = result.problems.filter((p) => p.level === "error");
      if (!result.tree) {
        this.setAttribute("data-state", "error");
        this.#root.render(<pre className="pp-problems">{formatProblems(problems)}</pre>);
        return;
      }
      view = viewOfNatural(result.tree, {
        ...DEFAULT_SETTINGS,
        fontSize: Number(this.getAttribute("font-size")) || DEFAULT_SETTINGS.fontSize,
        isUnlimitedWidth: this.hasAttribute("unlimited-width"),
      });
    }

    if (view.latexSettings.isActive) {
      await loadKatex();
      if (!this.#katexLink) {
        this.#katexLink = document.createElement("link");
        this.#katexLink.rel = "stylesheet";
        this.#katexLink.href = `${KATEX}.css`;
        this.#shadow.prepend(this.#katexLink);
      }
    }

    this.#naturalWidth = 0;
    this.#root?.render(<Tree key={++this.#renders} view={view} problems={problems} onLayout={() => this.#fit()}/>);
    this.setAttribute("data-state", problems.length ? "error" : "rendered");
  }

  #theme(): Theme {
    const picked = stored(THEME_KEY);
    if (isTheme(picked)) return picked;
    const attr = this.getAttribute("theme");
    return isTheme(attr) ? attr : "sand";
  }

  #darkBars(): boolean {
    const picked = stored(DARK_BARS_KEY);
    return picked === null ? this.hasAttribute("dark-bars") : picked === "1";
  }

  #openMenu(event: MouseEvent) {
    if (window.getSelection()?.toString()) return;
    event.preventDefault();
    this.#closeMenu();
    const host = this.getBoundingClientRect();
    const menu = document.createElement("div");
    menu.className = "pp-menu";
    menu.style.left = `${event.clientX - host.left}px`;
    menu.style.top = `${event.clientY - host.top}px`;
    this.#menu = menu;
    this.#fillMenu();
    this.#shadow.append(menu);
    const close = (e: Event) => {
      if (e instanceof KeyboardEvent && e.key !== "Escape") return;
      if (e.type === "mousedown" && e.composedPath().includes(menu)) return;
      this.#closeMenu();
      document.removeEventListener("mousedown", close);
      document.removeEventListener("keydown", close);
    };
    document.addEventListener("mousedown", close);
    document.addEventListener("keydown", close);
  }

  #fillMenu() {
    if (!this.#menu) return;
    const item = (label: string, isChecked: boolean, pick: () => void) => {
      const button = document.createElement("button");
      button.type = "button";
      const mark = document.createElement("span");
      mark.className = "pp-menu-mark";
      mark.textContent = isChecked ? "✓" : "";
      button.append(mark, label);
      button.addEventListener("click", () => { pick(); PaperproofProofElement.renderAll(); this.#fillMenu(); });
      return button;
    };
    const theme = this.#theme();
    this.#menu.replaceChildren(
      ...THEMES.map((name) => item(THEME_LABELS[name], name === theme, () => store(THEME_KEY, name))),
      document.createElement("hr"),
      item("Dark bars", this.#darkBars(), () => store(DARK_BARS_KEY, this.#darkBars() ? "0" : "1")),
    );
  }

  #closeMenu() {
    this.#menu?.remove();
    this.#menu = null;
  }

  #fit() {
    const wrap = this.#shadow.querySelector(".pp-wrap");
    if (!wrap) return;
    this.#resizeObserver.observe(wrap);
    this.#rootEl.classList.add("-measuring");
    const width = Math.ceil(wrap.getBoundingClientRect().width);
    this.#rootEl.classList.remove("-measuring");
    this.setAttribute("data-width", String(Math.ceil(wrap.getBoundingClientRect().width)));
    this.setAttribute("data-height", String(Math.ceil(this.getBoundingClientRect().height)));
    if (width === this.#naturalWidth) return;
    this.#naturalWidth = width;
    let css = "";
    if (this.getAttribute("fit") !== "scroll" && this.getAttribute("fit") !== "none") {
      for (let column = width - 1; column > width / 4; column -= FIT_STEP) {
        css += `@container (max-width: ${column}px) { .proof-tree { zoom: ${((column - FIT_STEP) / width).toFixed(4)}; } }\n`;
      }
    }
    this.#fitStyle.textContent = css;
  }
}

window.Paperproof = { version: PP_VERSION, validate };
window.addEventListener("storage", (event) => {
  if (event.key === THEME_KEY || event.key === DARK_BARS_KEY) PaperproofProofElement.renderAll();
});
if (!customElements.get("paperproof-proof")) customElements.define("paperproof-proof", PaperproofProofElement);
