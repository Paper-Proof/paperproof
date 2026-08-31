// Faithful TypeScript port of paperproof-mcp's lean_runner.py layout logic.
//
// Given the user's Lean source + a bundled parser source, produce the "shadow"
// document text: the parser injected right after the file's imports, plus the
// line offset so we can map a cursor position in the real file to the shadow.
//
// Two Lean layouts are supported (see lean_runner.py for the full rationale):
//   - Classic files (`import` at the top): parser injected as ordinary decls.
//   - Module-system files (`module` / `public import`): compile-time code must
//     be `meta`, with its dependencies `meta import`ed.

const DECL_RE =
  /^(\s*)(public |private )?(partial |noncomputable )?(def|structure|instance|abbrev|inductive) /;

const isImportLine = (stripped: string): boolean =>
  stripped.startsWith("import ") || stripped.startsWith("public import ");

/** True if `module` is the first real token (skipping leading comments/blanks). */
export const usesModuleSystem = (lines: string[]): boolean => {
  let inBlock = false;
  for (const line of lines) {
    const s = line.trim();
    if (inBlock) {
      if (s.includes("-/")) { inBlock = false; }
      continue;
    }
    if (s === "" || s.startsWith("--")) { continue; }
    if (s.startsWith("/-")) {
      if (!s.includes("-/")) { inBlock = true; }
      continue;
    }
    return s === "module";
  }
  return false;
};

/** Index of the last `import`/`public import` line, or -1 if there are none. */
export const lastImportLine = (lines: string[]): number => {
  let idx = -1;
  lines.forEach((l, i) => {
    if (isImportLine(l.trim())) { idx = i; }
  });
  return idx;
};

/** Mark every parser declaration `meta`, keeping its `public`/`private` visibility. */
const metaize = (body: string): string =>
  body
    .split("\n")
    .map((line) => {
      const m = DECL_RE.exec(line);
      if (!m) { return line; }
      const indent = m[1] ?? "";
      const visibility = m[2] ?? ""; // keep `public `/`private ` (name mangling otherwise)
      const partial = m[3] ?? "";
      return `${indent}${visibility}meta ${partial}${m[4]} ${line.slice(m[0].length)}`;
    })
    .join("\n");

const parserImportsAndBody = (parserSource: string): { imports: string[]; body: string } => {
  const all = parserSource.split("\n");
  const imports = all.filter((l) => l.trim().startsWith("import "));
  const body = all.filter((l) => !l.trim().startsWith("import ")).join("\n");
  return { imports, body };
};

export interface Injection {
  /** Full shadow document text: source with the parser injected after imports. */
  shadowText: string;
  /** 0-based line index at which the parser block was inserted. */
  insertedAt: number;
  /** Number of lines the parser block added. */
  injectedLineCount: number;
  module: boolean;
}

/**
 * Build the shadow text for `sourceText`, injecting `parserSource` after the
 * file's imports. Mirrors lean_runner.extract_proof_tree's edit construction.
 */
export const buildInjection = (sourceText: string, parserSource: string): Injection => {
  const lines = sourceText.split("\n");
  const module = usesModuleSystem(lines);
  const { imports: parserImports, body } = parserImportsAndBody(parserSource);

  let block: string;
  if (module) {
    const fileImports = lines
      .filter((l) => isImportLine(l.trim()))
      .map((l) => l.trim().replace(/^public import/, "import"));
    const metaImports = [
      ...fileImports.map((fi) => `meta ${fi}`),
      "meta import Lean",
      "meta import Lean.Meta.Basic",
      "meta import Lean.Meta.CollectMVars",
      "meta import Lean.Server.Requests",
    ];
    block = metaImports.join("\n") + "\n" + metaize(body) + "\n";
  } else {
    block = parserImports.join("\n") + "\n" + body + "\n";
  }

  const lastImport = lastImportLine(lines);
  const insertedAt = lastImport >= 0 ? lastImport + 1 : 0;

  const shadowLines = [...lines.slice(0, insertedAt), block.replace(/\n$/, ""), ...lines.slice(insertedAt)];
  const shadowText = shadowLines.join("\n");
  const injectedLineCount = block.split("\n").length - 1; // block ends in "\n"

  return { shadowText, insertedAt, injectedLineCount, module };
};

/**
 * Map a position in the real file to the equivalent position in the shadow.
 * A line at/after the injection point shifts down by the injected line count.
 * Also nudges column 0 to just inside the first token, matching lean_runner
 * (at a command boundary `withWaitFindSnapAtPos` resolves col 0 to the previous
 * command's trailing edge).
 */
export const mapPosition = (
  injection: Injection,
  line: number,
  character: number,
  sourceLines: string[]
): { line: number; character: number } => {
  let ch = character;
  if (ch === 0 && line >= 0 && line < sourceLines.length) {
    const raw = sourceLines[line];
    const indent = raw.length - raw.trimStart().length;
    if (indent < raw.length) { ch = indent + 1; }
  }
  const shifted = line >= injection.insertedAt ? line + injection.injectedLineCount : line;
  return { line: shifted, character: ch };
};
