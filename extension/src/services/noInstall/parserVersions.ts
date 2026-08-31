// Picks which bundled parser to inject, based on the project's lean-toolchain.
// Port of paperproof-mcp's candidate_parsers: exact match wins; otherwise try
// [nearest floor, nearest ceil] (an older-Lean parser usually still compiles on
// a newer Lean, so floor is tried first, ceil is the backup).

import * as fs from "fs";
import * as path from "path";
import * as vscode from "vscode";

export interface ParserCandidate {
  version: string;
  source: string;
}

const parsersDir = (context: vscode.ExtensionContext): string =>
  path.join(context.extensionUri.fsPath, "parsers");

const availableVersions = (context: vscode.ExtensionContext): string[] => {
  const dir = parsersDir(context);
  if (!fs.existsSync(dir)) { return []; }
  return fs
    .readdirSync(dir)
    .filter((f) => /^v\d+\.\d+\.\d+.*\.lean$/.test(f))
    .map((f) => f.replace(/^v/, "").replace(/\.lean$/, ""))
    .sort();
};

const versionKey = (v: string): number[] =>
  v.split("-")[0].split(".").map((x) => parseInt(x, 10));

const cmpKey = (a: number[], b: number[]): number => {
  for (let i = 0; i < Math.max(a.length, b.length); i++) {
    const d = (a[i] ?? 0) - (b[i] ?? 0);
    if (d !== 0) { return d; }
  }
  return 0;
};

/** Find the project root (nearest ancestor with a lean-toolchain) for a file. */
export const findProjectRoot = (filePath: string): string | null => {
  let current = path.dirname(filePath);
  // eslint-disable-next-line no-constant-condition
  while (true) {
    if (fs.existsSync(path.join(current, "lean-toolchain"))) { return current; }
    const parent = path.dirname(current);
    if (parent === current) { return null; }
    current = parent;
  }
};

export const readToolchainVersion = (projectRoot: string): string | null => {
  const tc = path.join(projectRoot, "lean-toolchain");
  if (!fs.existsSync(tc)) { return null; }
  const m = /v(\d+\.\d+\.\d+(?:-\w+)?)/.exec(fs.readFileSync(tc, "utf-8").trim());
  return m ? m[1] : null;
};

export interface CandidateResult {
  projectVersion: string | null;
  candidates: ParserCandidate[];
}

export const candidateParsers = (
  context: vscode.ExtensionContext,
  projectRoot: string
): CandidateResult => {
  const versions = availableVersions(context);
  if (versions.length === 0) {
    throw new Error("No Lean parsers are bundled with the extension.");
  }
  const pv = readToolchainVersion(projectRoot);

  let chosen: string[];
  if (pv && versions.includes(pv)) {
    chosen = [pv];
  } else if (pv) {
    const floors = versions
      .filter((v) => cmpKey(versionKey(v), versionKey(pv)) < 0)
      .sort((a, b) => cmpKey(versionKey(b), versionKey(a)));
    const ceils = versions
      .filter((v) => cmpKey(versionKey(v), versionKey(pv)) > 0)
      .sort((a, b) => cmpKey(versionKey(a), versionKey(b)));
    chosen = [...(floors[0] ? [floors[0]] : []), ...(ceils[0] ? [ceils[0]] : [])];
  } else {
    chosen = [versions.slice().sort((a, b) => cmpKey(versionKey(a), versionKey(b))).pop()!];
  }

  const dir = parsersDir(context);
  return {
    projectVersion: pv,
    candidates: chosen.map((v) => ({
      version: v,
      source: fs.readFileSync(path.join(dir, `v${v}.lean`), "utf-8"),
    })),
  };
};
