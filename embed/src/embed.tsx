import { validate } from "@app/format";
import type { PaperproofFit, PaperproofTheme } from "../react";
import { ShadowTree } from "./ShadowTree";

declare const PP_VERSION: string;

declare global {
  interface Window { Paperproof?: { version: string; validate: typeof validate } }
}

class PaperproofProofElement extends HTMLElement {
  static observedAttributes = ["theme", "dark-bars", "fit", "font-size", "unlimited-width"];

  #tree: ShadowTree | null = null;
  #proof: unknown = undefined;
  #hasProof = false;

  constructor() {
    super();
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
    this.#render();
  }

  connectedCallback() {
    if (document.readyState === "loading") {
      document.addEventListener("DOMContentLoaded", () => this.#mount(), { once: true });
    } else {
      this.#mount();
    }
  }

  disconnectedCallback() {
    this.#tree?.unmount();
    this.#tree = null;
  }

  attributeChangedCallback() {
    this.#render();
  }

  async #mount() {
    if (this.#tree || !this.isConnected) return;
    this.#tree = new ShadowTree(this);
    if (this.#hasProof) return this.#render();
    try {
      const proof = await this.#readProof();
      if (!this.#hasProof) this.proof = proof;
    } catch (e) {
      if (!this.#hasProof) this.#tree?.render({ proof: null, error: e instanceof Error ? e.message : String(e) });
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

  #render() {
    if (!this.#tree || !this.#hasProof) return;
    this.#tree.render({
      proof: this.#proof,
      theme: (this.getAttribute("theme") ?? undefined) as PaperproofTheme | undefined,
      darkBars: this.hasAttribute("dark-bars"),
      fontSize: Number(this.getAttribute("font-size")) || undefined,
      unlimitedWidth: this.hasAttribute("unlimited-width"),
      fit: (this.getAttribute("fit") ?? undefined) as PaperproofFit | undefined,
    });
  }
}

window.Paperproof = { version: PP_VERSION, validate };
if (!customElements.get("paperproof-proof")) customElements.define("paperproof-proof", PaperproofProofElement);
