import esbuild from "esbuild";
import path from "path";
import fs from "fs";
import { execSync } from "child_process";
import { fileURLToPath } from "url";

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

const appSrc = path.resolve(__dirname, "../app/src");

// Shared options for both website bundles
const appNodeModules = path.resolve(__dirname, "../app/node_modules");

const shared = {
  bundle: true,
  sourcemap: true,
  platform: "browser",
  tsconfig: path.resolve(__dirname, "../app/tsconfig.json"),
  // React, monaco-editor, etc. live in app/node_modules — no need to duplicate them here
  nodePaths: [appNodeModules],
  // Pin react/react-dom to the app's single copy so we never get two React instances
  // (installing @monaco-editor/react hoists react into paperproof.xyz/node_modules,
  //  which esbuild would otherwise pick up first)
  alias: {
    "react":     path.resolve(appNodeModules, "react"),
    "react-dom": path.resolve(appNodeModules, "react-dom"),
  },
  loader: {
    ".json": "json",
    ".css": "css",
    ".woff": "dataurl",
    ".woff2": "dataurl",
    ".ttf": "dataurl",
  },
  plugins: [aliasPlugin()],
  logLevel: "info",
  define: { "process.env.NODE_ENV": '"production"' },
  minify: false,
  external: ["stream", "zlib", "url", "http", "events", "crypto", "tls", "https", "net", "buffer", "os", "path", "fs"],
};

function aliasPlugin() {
  return {
    name: "alias",
    setup(build) {
      // @app/* → app/src/*, with proper extension + index resolution
      build.onResolve({ filter: /^@app\// }, args => {
        const base = path.resolve(appSrc, args.path.slice("@app/".length));
        for (const suffix of [".ts", ".tsx", "/index.ts", "/index.tsx", ""]) {
          const p = base + suffix;
          try { if (fs.statSync(p).isFile()) return { path: p }; } catch {}
        }
        return { path: base };
      });

      // src/indexBrowser → shared proof context (used by BoxEl internals)
      build.onResolve({ filter: /^src\/indexBrowser$/ }, () => ({
        path: path.resolve(__dirname, "src/proofContext.tsx"),
      }));
    },
  };
}

const watch = process.argv.includes("--watch");

// [Claude comment] Snapshot pages get their own bundle - reusing the playground's
// would ship all of monaco-editor to readers who only need the proof tree.
const bundles = [
  { name: "landingPage",        entry: "src/landingPage.tsx" },
  { name: "standaloneRenderer", entry: "src/standaloneRenderer.tsx", logLimit: 0 },
  { name: "snapshotRenderer",   entry: "src/snapshotRenderer.tsx" },
];

const optionsFor = ({ name, entry, logLimit }) => ({
  ...shared,
  ...(logLimit === undefined ? {} : { logLimit }),
  entryPoints: [entry],
  outfile: `public/dist/${name}.js`,
});

if (watch) {
  const contexts = await Promise.all(bundles.map((bundle) => esbuild.context(optionsFor(bundle))));
  await Promise.all(contexts.map((ctx) => ctx.watch()));
  console.log("watching...");
} else {
  await Promise.all(bundles.map((bundle) =>
    esbuild.build(optionsFor(bundle)).then(() => console.log(`✓ ${bundle.name}`))
  ));

  // Pre-render landing page so crawlers and AI agents see real content
  fs.mkdirSync(path.resolve(__dirname, "tmp"), { recursive: true });
  await esbuild.build({
    bundle: true,
    platform: "node",
    format: "cjs",
    tsconfig: path.resolve(__dirname, "../app/tsconfig.json"),
    nodePaths: [appNodeModules],
    alias: {
      "react":     path.resolve(appNodeModules, "react"),
      "react-dom": path.resolve(appNodeModules, "react-dom"),
    },
    loader: { ".json": "json", ".css": "empty", ".woff": "dataurl", ".woff2": "dataurl", ".ttf": "dataurl" },
    plugins: [aliasPlugin()],
    define: { "process.env.NODE_ENV": '"production"' },
    external: ["stream", "zlib", "url", "http", "events", "crypto", "tls", "https", "net", "buffer", "os", "path", "fs"],
    entryPoints: ["src/prerender.tsx"],
    outfile: "tmp/prerender.cjs",
  });
  execSync("node tmp/prerender.cjs", { stdio: "inherit", cwd: __dirname });
  console.log("✓ prerendered index.html");
}
