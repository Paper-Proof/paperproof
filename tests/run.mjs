// node tests/run.mjs                      build every frontend, type-check, validate tests/proofs/
// node tests/run.mjs --screenshots <dir>  ...and screenshot every proof in tests/proofs/
// node tests/run.mjs --compare <dir>      ...and compare the screenshots with <dir>

import fs from "fs";
import os from "os";
import path from "path";
import { spawn, spawnSync } from "child_process";
import { fileURLToPath, pathToFileURL } from "url";

const repo = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const appAlias = {
  name: "app-alias",
  setup(build) {
    build.onResolve({ filter: /^@app\// }, (a) => {
      const base = path.join(repo, "app/src", a.path.slice("@app/".length));
      for (const suffix of [".ts", ".tsx", "/index.ts", "/index.tsx", ""]) if (fs.existsSync(base + suffix) && fs.statSync(base + suffix).isFile()) return { path: base + suffix };
      return { path: base };
    });
  },
};
const args = process.argv.slice(2);
const opt = (name) => { const i = args.indexOf(name); return i >= 0 ? args[i + 1] : undefined; };
const screenshotsDir = opt("--screenshots") ?? opt("--compare");
const compareDir = opt("--compare") ? path.resolve(opt("--compare")) : null;

let failed = false;
const step = (label, cmd, cmdArgs, cwd) => {
  process.stdout.write(`${label} … `);
  const r = spawnSync(cmd, cmdArgs, { cwd: path.join(repo, cwd), encoding: "utf8" });
  if (r.status === 0) { console.log("ok"); return r.stdout; }
  failed = true;
  console.log(`FAILED\n${(r.stdout + r.stderr).trim().replace(/^/gm, "  ")}`);
  return null;
};

step("extension webview build", process.execPath, ["esbuild.prod.js"], "app");
step("paperproof.xyz build", process.execPath, ["esbuild.js"], "paperproof.xyz");
const hasEmbed = fs.existsSync(path.join(repo, "embed/build.mjs"));
if (hasEmbed) {
  step("embed build", process.execPath, ["build.mjs"], "embed");
  process.stdout.write("/embed/skill is up to date … ");
  const stale = spawnSync("git", ["status", "--porcelain", "--", "embed/skill"], { cwd: repo, encoding: "utf8" }).stdout.trim();
  if (!stale) console.log("ok");
  else { failed = true; console.log(`FAILED: the build changed it - commit it\n${stale.replace(/^/gm, "  ")}`); }
}
step("type check app/", path.join(repo, "app/node_modules/.bin/tsc"), ["--noEmit", "-p", "."], "app");
if (hasEmbed) step("type check embed/", path.join(repo, "app/node_modules/.bin/tsc"), ["-p", "."], "embed");

const proofFiles = fs.readdirSync(path.join(repo, "tests/proofs")).filter((f) => f.endsWith(".json")).sort();
const leanFiles = fs.readdirSync(path.join(repo, "tests/lean")).filter((f) => f.endsWith(".json")).sort();
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "paperproof-tests-"));
const lib = await loadLib();

process.stdout.write(`validate ${proofFiles.length} proofs … `);
const invalid = proofFiles.map((file) => {
  const result = lib.validate(JSON.parse(fs.readFileSync(path.join(repo, "tests/proofs", file), "utf8")));
  return result.problems.length ? `${file}\n${lib.formatProblems(result.problems).replace(/^/gm, "  ")}` : null;
}).filter(Boolean);
if (invalid.length === 0) console.log("ok");
else { failed = true; console.log(`FAILED\n${invalid.join("\n").replace(/^/gm, "  ")}`); }

if (screenshotsDir && !failed) await screenshots();
if (!compareDir || !failed) fs.rmSync(tmp, { recursive: true, force: true });
process.exitCode = failed ? 1 : 0;

async function loadLib() {
  const { default: esbuild } = await import(pathToFileURL(path.join(repo, "paperproof.xyz/node_modules/esbuild/lib/main.js")).href);
  await esbuild.build({
    entryPoints: [path.join(repo, "tests/lib.ts")],
    bundle: true, platform: "node", format: "esm", logLevel: "warning",
    outfile: path.join(tmp, "lib.mjs"),
    tsconfig: path.join(repo, "app/tsconfig.json"),
    plugins: [appAlias],
  });
  return import(pathToFileURL(path.join(tmp, "lib.mjs")).href);
}

async function screenshots() {
  const outDir = compareDir ? path.join(tmp, "now") : path.resolve(screenshotsDir);
  fs.mkdirSync(outDir, { recursive: true });
  const { snapshotPayload } = lib;

  const { default: esbuild } = await import(pathToFileURL(path.join(repo, "paperproof.xyz/node_modules/esbuild/lib/main.js")).href);
  const appNodeModules = path.join(repo, "app/node_modules");
  await esbuild.build({
    entryPoints: [path.join(repo, "tests/vscode.tsx")],
    bundle: true, platform: "browser", logLevel: "warning",
    outdir: tmp,
    tsconfig: path.join(repo, "app/tsconfig.json"),
    nodePaths: [appNodeModules],
    alias: { react: path.join(appNodeModules, "react"), "react-dom": path.join(appNodeModules, "react-dom") },
    loader: { ".css": "css", ".woff": "dataurl", ".woff2": "dataurl", ".ttf": "dataurl" },
    define: { "process.env.NODE_ENV": '"production"', IS_VSCODE: "false" },
    plugins: [appAlias],
  });

  if (hasEmbed) await esbuild.build({
    entryPoints: [path.join(repo, "tests/react.tsx")],
    bundle: true, platform: "browser", logLevel: "warning",
    outdir: tmp,
    tsconfig: path.join(repo, "app/tsconfig.json"),
    alias: { react: path.join(appNodeModules, "react"), "react-dom": path.join(appNodeModules, "react-dom") },
    define: { "process.env.NODE_ENV": '"production"' },
  });

  const dist = (f) => pathToFileURL(path.join(repo, "paperproof.xyz/public/dist", f)).href;
  const inline = (x) => JSON.stringify(x).replace(/</g, "\\u003c");
  const still = "<style>*, *::before, *::after { animation: none !important; transition: none !important; }</style>";
  const snapshotPage = (payload) => `<!DOCTYPE html><html lang="en"><head><meta charset="UTF-8">
<style>body { margin: 0; padding: 20px; background: white; }</style>
<script src="${dist("paperproof-embed.js")}"></script></head>
<body><paperproof-proof fit="none" theme="cyan"><script type="application/json">${inline(payload)}</script></paperproof-proof></body></html>`;
  const vscodePage = (payload) => `<!DOCTYPE html><html lang="en"><head><meta charset="UTF-8">
<link rel="stylesheet" href="${pathToFileURL(path.join(tmp, "vscode.css")).href}">
<style>body { --vscode-editor-font-family: monospace; --vscode-editor-background: #fff; }</style>${still}</head>
<body class="vscode-light"><div id="root"></div>
<script>window.PAPERPROOF_SNAPSHOT = ${inline(payload)};</script>
<script src="${pathToFileURL(path.join(tmp, "vscode.js")).href}"></script></body></html>`;
  const playgroundPage = (proof) => `<!DOCTYPE html><html lang="en"><head><meta charset="utf-8">
<script>localStorage.setItem("paperproof-natural-json", ${inline(JSON.stringify(proof))});</script>
<link rel="stylesheet" href="${dist("standaloneRenderer.css")}">${still}</head>
<body class="standalone"><div id="root"></div>
<script src="${dist("paperproof-embed.js")}"></script><script src="${dist("standaloneRenderer.js")}"></script></body></html>`;

  const embedPage = (proof) => `<!DOCTYPE html><html lang="en"><head><meta charset="utf-8">
<script src="${pathToFileURL(path.join(repo, "embed/dist/paperproof-embed.js")).href}"></script></head>
<body style="margin: 20px; background: #fff"><paperproof-proof><script type="application/json">${JSON.stringify(proof).replace(/<\//g, "<\\/")}</script></paperproof-proof></body></html>`;

  const reactPage = (proof) => `<!DOCTYPE html><html lang="en"><head><meta charset="utf-8">
</head>
<body style="margin: 20px; background: #fff"><div id="root"></div>
<script>window.PAPERPROOF_PROOF = ${inline(proof)};</script>
<script src="${pathToFileURL(path.join(tmp, "react.js")).href}"></script></body></html>`;

  const pages = [];
  for (const file of proofFiles) {
    const proof = JSON.parse(fs.readFileSync(path.join(repo, "tests/proofs", file), "utf8"));
    const name = file.replace(/\.json$/, "");
    pages.push([`${name}.snapshot`, snapshotPage(snapshotPayload(proof))]);
    pages.push([`${name}.snapshot-wider`, snapshotPage(snapshotPayload(proof, { isUnlimitedWidth: true }))]);
    pages.push([`${name}.vscode`, vscodePage(snapshotPayload(proof))]);
    pages.push([`${name}.playground`, playgroundPage(proof)]);
    if (hasEmbed) pages.push([`${name}.embed`, embedPage(proof)]);
    if (hasEmbed) pages.push([`${name}.react`, reactPage(proof)]);
  }
  if (hasEmbed) for (const file of leanFiles) {
    const proof = JSON.parse(fs.readFileSync(path.join(repo, "tests/lean", file), "utf8"));
    const name = `lean-${file.replace(/\.json$/, "")}`;
    pages.push([`${name}.embed`, embedPage(proof)]);
    pages.push([`${name}.react`, reactPage(proof)]);
  }

  const chrome = process.env.CHROME_PATH ?? ["google-chrome", "google-chrome-stable", "chromium", "chromium-browser"]
    .find((c) => spawnSync("which", [c]).status === 0);
  if (!chrome) { console.log("screenshots … FAILED: Chrome not found, set CHROME_PATH"); failed = true; return; }
  const shoot = ([name, html]) => new Promise((resolve) => {
    const page = path.join(tmp, `${name}.html`);
    fs.writeFileSync(page, html);
    const p = spawn(chrome, ["--headless=new", "--disable-gpu", "--hide-scrollbars", "--allow-file-access-from-files",
      "--virtual-time-budget=8000", "--window-size=1100,2400", `--screenshot=${path.join(outDir, `${name}.png`)}`,
      pathToFileURL(page).href], { stdio: "ignore" });
    p.on("close", resolve);
  });
  process.stdout.write(`screenshots of ${pages.length} pages … `);
  const queue = [...pages];
  await Promise.all(Array.from({ length: 4 }, async () => { while (queue.length) await shoot(queue.shift()); }));
  console.log(compareDir ? "taken" : `ok, in ${outDir}`);

  if (compareDir) {
    const changed = [];
    for (const [name] of pages) {
      const before = path.join(compareDir, `${name}.png`), now = path.join(outDir, `${name}.png`);
      if (!fs.existsSync(before)) { changed.push(`${name}: not in ${compareDir}`); continue; }
      const r = spawnSync("compare", ["-metric", "AE", before, now, path.join(tmp, `${name}.diff.png`)], { encoding: "utf8" });
      const pixels = Number.parseFloat(r.stderr);
      if (pixels !== 0) changed.push(`${name}: ${Number.isNaN(pixels) ? r.stderr.trim() : `${pixels} pixels differ`}`);
    }
    if (changed.length === 0) console.log(`compare with ${compareDir} … ok, every page is identical`);
    else {
      failed = true;
      console.log(`compare with ${compareDir} … ${changed.length} changed (screenshots and diffs in ${tmp})\n${changed.map((c) => `  ${c}`).join("\n")}`);
    }
  }
}
