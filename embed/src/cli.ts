import fs from "fs";
import os from "os";
import path from "path";
import { spawnSync } from "child_process";
import { pathToFileURL } from "url";
import { validate, formatProblems, naturalProofTreeJsonSchema } from "@app/format";

declare const PP_VERSION: string;

const USAGE = `paperproof-embed ${PP_VERSION}

  validate <file>...          check proofs; a .json file is one proof, any other file
                              (.html, .md, ...) is searched for <paperproof-proof> blocks
  render <file> [options]     render one proof to a PNG with headless Chrome
      --out <file.png>        default: <file>.png (or <file>-<index>.png)
      --index <n>             which <paperproof-proof> block of the file (default 0)
      --width <px>            page width (default 1000)
  schema                      print the JSON Schema of the proof format
  instructions                print the instructions for writing proofs (for LLMs)

Exit code 1 if any proof has errors. Set CHROME_PATH if Chrome isn't found.`;

interface Found { proof: unknown; where: string; attrs: string; parseError?: string }

const lineOf = (text: string, index: number) => text.slice(0, index).split("\n").length;

const findProofs = (file: string): Found[] => {
  const text = fs.readFileSync(file, "utf8");
  const parse = (json: string, where: string, attrs = ""): Found => {
    try { return { proof: JSON.parse(json), where, attrs }; }
    catch (e) { return { proof: null, where, attrs, parseError: e instanceof Error ? e.message : String(e) }; }
  };
  if (file.endsWith(".json")) return [parse(text, file)];

  const found: Found[] = [];
  const block = /<paperproof-proof\b([^>]*)>([\s\S]*?)<\/paperproof-proof>/g;
  for (let m: RegExpExecArray | null; (m = block.exec(text)); ) {
    const where = `${file}:${lineOf(text, m.index)}`;
    const attrs = m[1].replace(/\bsrc=["'][^"']*["']/, "").trim();
    const script = /<script\b[^>]*type=["']application\/json["'][^>]*>([\s\S]*?)<\/script>/.exec(m[2]);
    if (!script) {
      const src = /\bsrc=["']([^"']+)["']/.exec(m[1]);
      if (src) found.push(...findProofs(path.resolve(path.dirname(file), src[1])).map((f) => ({ ...f, where: `${where} → ${f.where}`, attrs })));
      else found.push({ proof: null, where, attrs, parseError: 'no <script type="application/json"> inside <paperproof-proof>' });
      continue;
    }
    found.push(parse(script[1], where, attrs));
  }
  return found;
};

const cmdValidate = (files: string[]) => {
  if (files.length === 0) { console.error(USAGE); return 2; }
  let errors = 0, warnings = 0, proofs = 0;
  for (const file of files) {
    const found = findProofs(file);
    if (found.length === 0) console.log(`${file}: no <paperproof-proof> blocks`);
    found.forEach((f, i) => {
      proofs++;
      const label = found.length > 1 ? `${f.where} (proof ${i})` : f.where;
      if (f.parseError) {
        errors++;
        console.log(`${label}\n  error   (root): invalid JSON: ${f.parseError}`);
        return;
      }
      const result = validate(f.proof);
      errors += result.problems.filter((p) => p.level === "error").length;
      warnings += result.problems.filter((p) => p.level === "warning").length;
      console.log(result.problems.length === 0
        ? `${label}: ok`
        : `${label}\n${formatProblems(result.problems).replace(/^/gm, "  ")}`);
    });
  }
  console.log(`\n${proofs} proof(s), ${errors} error(s), ${warnings} warning(s)`);
  return errors > 0 ? 1 : 0;
};

const findChrome = (): string => {
  if (process.env.CHROME_PATH) return process.env.CHROME_PATH;
  const candidates = process.platform === "darwin"
    ? ["/Applications/Google Chrome.app/Contents/MacOS/Google Chrome", "/Applications/Chromium.app/Contents/MacOS/Chromium"]
    : process.platform === "win32"
      ? ["C:\\Program Files\\Google\\Chrome\\Application\\chrome.exe", "C:\\Program Files (x86)\\Google\\Chrome\\Application\\chrome.exe"]
      : ["google-chrome", "google-chrome-stable", "chromium", "chromium-browser"];
  for (const c of candidates) {
    if (path.isAbsolute(c) ? fs.existsSync(c) : spawnSync("which", [c]).status === 0) return c;
  }
  throw new Error("Chrome not found; set CHROME_PATH");
};

const proofElement = (found: Found) =>
  `<paperproof-proof ${found.attrs}><script type="application/json">${JSON.stringify(found.proof).replace(/<\//g, "<\\/")}</script></paperproof-proof>`;

const cmdRender = (args: string[]) => {
  const opt = (name: string) => { const i = args.indexOf(name); return i >= 0 ? args[i + 1] : undefined; };
  const file = args.find((a, i) => !a.startsWith("--") && !args[i - 1]?.startsWith("--"));
  if (!file) { console.error(USAGE); return 2; }
  const index = Number(opt("--index") ?? 0);
  const width = Number(opt("--width") ?? 1000);
  const found = findProofs(file)[index];
  if (!found) { console.error(`${file}: no proof with index ${index}`); return 2; }
  if (found.parseError) { console.error(`${found.where}: invalid JSON: ${found.parseError}`); return 1; }
  const out = path.resolve(opt("--out") ?? file.replace(/\.[^.]+$/, "") + (file.endsWith(".json") ? "" : `-${index}`) + ".png");

  const embedJs = path.join(__dirname, "paperproof-embed.js");
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "paperproof-"));
  const page = path.join(dir, "proof.html");
  fs.writeFileSync(page, `<!doctype html><html><head><meta charset="utf-8">
<style>html,body{margin:0;background:#fff}</style>
<script src="${pathToFileURL(embedJs).href}"></script></head><body>
${proofElement(found)}
</body></html>`);

  const chrome = findChrome();
  const base = ["--headless=new", "--disable-gpu", "--hide-scrollbars", "--allow-file-access-from-files", "--virtual-time-budget=5000"];
  const dom = spawnSync(chrome, [...base, `--window-size=${width},3000`, "--dump-dom", pathToFileURL(page).href], { encoding: "utf8" });
  const height = Number(/data-height="(\d+)"/.exec(dom.stdout ?? "")?.[1]);
  const state = /data-state="(\w+)"/.exec(dom.stdout ?? "")?.[1];
  const treeWidth = Math.min(width, Number(/data-width="(\d+)"/.exec(dom.stdout ?? "")?.[1]) || width);
  if (!height) { console.error(`render failed:\n${dom.stderr}`); return 1; }
  const shotWidth = state === "error" ? width : treeWidth;
  spawnSync(chrome, [...base, `--window-size=${shotWidth},${height}`, `--screenshot=${out}`, pathToFileURL(page).href], { encoding: "utf8" });
  fs.rmSync(dir, { recursive: true, force: true });
  console.log(`${out} (${shotWidth}×${height}${state === "error" ? ", the proof has errors - run validate" : ""})`);
  return state === "error" ? 1 : 0;
};

const main = (argv: string[]) => {
  const [cmd, ...rest] = argv;
  switch (cmd) {
    case "validate": return cmdValidate(rest);
    case "render": return cmdRender(rest);
    case "schema": console.log(JSON.stringify(naturalProofTreeJsonSchema(), null, 2)); return 0;
    case "instructions": process.stdout.write(fs.readFileSync(path.join(__dirname, "llms.txt"), "utf8")); return 0;
    case "--version": case "-v": console.log(PP_VERSION); return 0;
    default: console.log(USAGE); return cmd && cmd !== "--help" && cmd !== "-h" ? 2 : 0;
  }
};

process.exitCode = main(process.argv.slice(2));
