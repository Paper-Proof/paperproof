import path from "path";
import fs from "fs";
import { execFileSync } from "child_process";
import { fileURLToPath } from "url";
import esbuild from "esbuild";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repo = path.resolve(__dirname, "..");
const appSrc = path.join(repo, "app/src");
const appNodeModules = path.join(repo, "app/node_modules");

const pkg = JSON.parse(fs.readFileSync(path.join(__dirname, "package.json"), "utf8"));
const katexVersion = JSON.parse(fs.readFileSync(path.join(appNodeModules, "katex/package.json"), "utf8")).version;

const resolvePlugin = (css) => ({
  name: "paperproof-embed",
  setup(build) {
    build.onResolve({ filter: /^@app\// }, (args) => {
      const base = path.join(appSrc, args.path.slice("@app/".length));
      for (const suffix of [".ts", ".tsx", "/index.ts", "/index.tsx", ""]) {
        if (fs.existsSync(base + suffix) && fs.statSync(base + suffix).isFile()) return { path: base + suffix };
      }
      return { path: base };
    });
    build.onResolve({ filter: /^src\/indexBrowser$/ }, () => ({ path: path.join(__dirname, "src/proofContext.tsx") }));
    build.onResolve({ filter: /katex\.min\.css$/ }, () => ({ path: "katex-css", namespace: "pp-empty" }));
    build.onResolve({ filter: /^pp:css$/ }, () => ({ path: "css", namespace: "pp-css" }));
    build.onLoad({ filter: /.*/, namespace: "pp-css" }, () => ({ contents: css ?? "", loader: "text" }));
    build.onLoad({ filter: /.*/, namespace: "pp-empty" }, () => ({ contents: "", loader: css === null ? "css" : "js" }));
    if (css !== null) build.onLoad({ filter: /\.css$/ }, () => ({ contents: "", loader: "js" }));
  },
});

const shared = {
  bundle: true,
  platform: "browser",
  tsconfig: path.join(repo, "app/tsconfig.json"),
  nodePaths: [appNodeModules],
  alias: { react: path.join(appNodeModules, "react"), "react-dom": path.join(appNodeModules, "react-dom") },
  loader: { ".css": "css", ".woff": "dataurl", ".woff2": "dataurl", ".ttf": "dataurl" },
  define: {
    "process.env.NODE_ENV": '"production"',
    PP_VERSION: JSON.stringify(pkg.version),
    KATEX_VERSION: JSON.stringify(katexVersion),
  },
  logLevel: "warning",
};

fs.rmSync(path.join(__dirname, "dist"), { recursive: true, force: true });

const pass1 = await esbuild.build({
  ...shared,
  entryPoints: [path.join(__dirname, "src/embed.tsx")],
  outdir: path.join(__dirname, "dist"),
  write: false,
  plugins: [resolvePlugin(null)],
});
const css = pass1.outputFiles.find((f) => f.path.endsWith(".css")).text;

await esbuild.build({
  ...shared,
  entryPoints: [path.join(__dirname, "src/embed.tsx")],
  outfile: path.join(__dirname, "dist/paperproof-embed.js"),
  format: "iife",
  minify: true,
  legalComments: "none",
  alias: { ...shared.alias, katex: path.join(__dirname, "src/katexShim.ts") },
  plugins: [resolvePlugin(css)],
});

await esbuild.build({
  ...shared,
  platform: "node",
  format: "cjs",
  entryPoints: [path.join(__dirname, "src/cli.ts")],
  outfile: path.join(__dirname, "dist/cli.cjs"),
  banner: { js: "#!/usr/bin/env node" },
  plugins: [resolvePlugin(css)],
});
fs.chmodSync(path.join(__dirname, "dist/cli.cjs"), 0o755);

const { llmInstructions, fewShotExamples } = await import(path.join(appSrc, "format/llmInstructions.js"));
const examples = fewShotExamples.slice(0, 2).map((ex, i) =>
  `### Example ${i + 1}\n\n${ex.text}\n\n\`\`\`json\n${JSON.stringify(JSON.parse(ex.json), null, 2)}\n\`\`\``
).join("\n\n");
const skill = fs.readFileSync(path.join(__dirname, "src/skill.template.md"), "utf8")
  .replaceAll("{{VERSION}}", pkg.version)
  .replace("{{INSTRUCTIONS}}", () => llmInstructions.trim())
  .replace("{{EXAMPLES}}", () => examples);
fs.mkdirSync(path.join(__dirname, "skill/paperproof-notation"), { recursive: true });
fs.writeFileSync(path.join(__dirname, "skill/paperproof-notation/SKILL.md"), skill);
fs.writeFileSync(path.join(__dirname, "dist/llms.txt"), skill.replace(/^---[\s\S]*?---\n+/, ""));
fs.writeFileSync(path.join(__dirname, "dist/schema.json"),
  execFileSync(process.execPath, [path.join(__dirname, "dist/cli.cjs"), "schema"], { encoding: "utf8" }));

const kb = (f) => `${Math.round(fs.statSync(path.join(__dirname, f)).size / 1024)} KB`;
console.log(`dist/paperproof-embed.js (${kb("dist/paperproof-embed.js")}), dist/cli.cjs, dist/schema.json, dist/llms.txt, skill/paperproof-notation/SKILL.md`);
