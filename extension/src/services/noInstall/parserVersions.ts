import * as fs from "fs";
import * as path from "path";
import v4_25_0 from "../../../../lean/v4.25.0/Paperproof.lean";
import v4_27_0 from "../../../../lean/v4.27.0/Paperproof.lean";

export const findProjectRoot = (filePath: string): string | null => {
  let current = path.dirname(filePath);
  for (;;) {
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

// the same rule as /lean/lakefile.lean
export const parserFor = (leanVersion: string | null): string =>
  leanVersion && Number(leanVersion.split(".")[1]) < 27 ? v4_25_0 : v4_27_0;
