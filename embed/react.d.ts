import type { CSSProperties, ReactElement } from "react";

export type PaperproofTheme = "sand" | "cyan" | "check" | "square";

export type PaperproofFit = "scale" | "scroll" | "none";

export interface PaperproofPosition {
  line: number;
  character: number;
}

export interface PaperproofProps {
  proof: unknown;
  theme?: PaperproofTheme;
  darkBars?: boolean;
  fontSize?: number;
  unlimitedWidth?: boolean;
  fit?: PaperproofFit;
  position?: PaperproofPosition;
  className?: string;
  style?: CSSProperties;
}

export declare const Paperproof: (props: PaperproofProps) => ReactElement;
