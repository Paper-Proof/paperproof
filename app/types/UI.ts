import { Editor, TLShapeId } from "@tldraw/tldraw";
import { ConvertedProofTree } from "types";

// TLDRAW settings
export interface UIConfig {
  hideNulls: boolean
}

export interface UIShared {
  editor: Editor;
  uiConfig: UIConfig;
  proofTree: ConvertedProofTree;
  inBetweenMargin: number;
  framePadding: number;
}

// TLDRAW UI elements
export interface UIHypTree {
  level: number;
  tactic: UIElement;
  nodes: { node: UIElement, tree?: UIHypTree }[];
}

export interface UIElement {
  size: [number, number];
  draw: (x: number, y: number, prefferedWidth?: number) => void;
}

export interface UIIdElement extends UIElement {
  id: TLShapeId;
}

export type UINode = { text: string; id: string; name?: string; subNodes?: UINodeLayer[] };

export type UINodeLayer = UINode[];
