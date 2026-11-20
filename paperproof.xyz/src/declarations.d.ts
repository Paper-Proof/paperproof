declare module '*.css';

declare namespace JSX {
  interface IntrinsicElements {
    "paperproof-proof": React.DetailedHTMLProps<React.HTMLAttributes<HTMLElement>, HTMLElement> & {
      kind?: string; fit?: string; theme?: string; "dark-bars"?: boolean;
    };
  }
}
