import React, { useCallback, useEffect, useRef, useState, useSyncExternalStore } from "react";
import type { PaperproofTheme } from "../../../../react";

const THEMES = ["sand", "cyan", "check", "square"] as const satisfies readonly PaperproofTheme[];
const isTheme = (x: unknown): x is PaperproofTheme => THEMES.includes(x as PaperproofTheme);

const THEME_LABELS: Record<PaperproofTheme, string> = {
  sand: "Sand", cyan: "Cyan, with 🎉", check: "Green ✓", square: "■ after the text",
};

const THEME_KEY = "paperproof-theme";
const DARK_BARS_KEY = "paperproof-dark-bars";
const picks = new Map<string, string>();
const listeners = new Set<() => void>();

const stored = (key: string) => {
  try { return localStorage.getItem(key) ?? picks.get(key) ?? null; } catch { return picks.get(key) ?? null; }
};
const store = (key: string, value: string) => {
  picks.set(key, value);
  try { localStorage.setItem(key, value); } catch { /* blocked: this page only */ }
  listeners.forEach((listener) => listener());
};
const subscribe = (onChange: () => void) => {
  const onStorage = (event: StorageEvent) => { if (event.key === THEME_KEY || event.key === DARK_BARS_KEY) onChange(); };
  listeners.add(onChange);
  window.addEventListener("storage", onStorage);
  return () => { listeners.delete(onChange); window.removeEventListener("storage", onStorage); };
};

interface Props {
  x: number;
  y: number;
  theme: PaperproofTheme;
  darkBars: boolean;
  onClose: () => void;
}

const ThemeMenu = ({ x, y, theme, darkBars, onClose }: Props) => {
  const ref = useRef<HTMLDivElement>(null);
  useEffect(() => {
    const close = (event: Event) => {
      if (event instanceof KeyboardEvent && event.key !== "Escape") return;
      if (event.type === "mousedown" && ref.current && event.composedPath().includes(ref.current)) return;
      onClose();
    };
    document.addEventListener("mousedown", close);
    document.addEventListener("keydown", close);
    return () => {
      document.removeEventListener("mousedown", close);
      document.removeEventListener("keydown", close);
    };
  }, [onClose]);
  const item = (label: string, isChecked: boolean, pick: () => void) =>
    <button type="button" key={label} onClick={pick}><span className="pp-menu-mark">{isChecked ? "✓" : ""}</span>{label}</button>;
  return (
    <div className="pp-menu" ref={ref} style={{ left: x, top: y }}>
      {THEMES.map((name) => item(THEME_LABELS[name], name === theme, () => store(THEME_KEY, name)))}
      <hr/>
      {item("Dark bars", darkBars, () => store(DARK_BARS_KEY, darkBars ? "0" : "1"))}
    </div>
  );
};

export const useThemeMenu = (theme: unknown, darkBars: boolean | undefined) => {
  useEffect(() => {
    if (theme !== undefined && !isTheme(theme)) console.warn(`[paperproof] theme="${theme}" is not one of ${THEMES.join(", ")}`);
  }, [theme]);
  const pickedTheme = useSyncExternalStore(subscribe, () => stored(THEME_KEY), () => null);
  const pickedDarkBars = useSyncExternalStore(subscribe, () => stored(DARK_BARS_KEY), () => null);
  const look = {
    theme: isTheme(pickedTheme) ? pickedTheme : isTheme(theme) ? theme : "sand",
    darkBars: pickedDarkBars === null ? !!darkBars : pickedDarkBars === "1",
  };
  const [at, setAt] = useState<{ x: number; y: number } | null>(null);
  const close = useCallback(() => setAt(null), []);
  const onContextMenu = (event: React.MouseEvent<HTMLElement>) => {
    if (window.getSelection()?.toString()) return;
    event.preventDefault();
    const box = event.currentTarget.getBoundingClientRect();
    setAt({ x: event.clientX - box.left, y: event.clientY - box.top });
  };
  const menu = at && <ThemeMenu {...at} theme={look.theme} darkBars={look.darkBars} onClose={close}/>;
  return { look, onContextMenu, menu };
};
