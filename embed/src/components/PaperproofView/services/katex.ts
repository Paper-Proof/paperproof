import { useEffect, useState } from "react";

declare const KATEX_VERSION: string;

const KATEX = `https://cdn.jsdelivr.net/npm/katex@${KATEX_VERSION}/dist/katex.min`;
export const KATEX_CSS = `${KATEX}.css`;

let loading: Promise<void> | null = null;
const loadKatex = () => loading ??= new Promise<void>((resolve) => {
  const link = document.createElement("link");
  link.rel = "stylesheet";
  link.href = KATEX_CSS;
  document.head.appendChild(link);
  const script = document.createElement("script");
  script.src = `${KATEX}.js`;
  script.onload = script.onerror = () => resolve();
  document.head.appendChild(script);
});

export const useKatex = (isNeeded: boolean): boolean => {
  const [isLoaded, setIsLoaded] = useState(() => typeof window !== "undefined" && !!window.katex);
  useEffect(() => {
    if (isNeeded && !isLoaded) loadKatex().then(() => setIsLoaded(true));
  }, [isNeeded, isLoaded]);
  return !isNeeded || isLoaded;
};
