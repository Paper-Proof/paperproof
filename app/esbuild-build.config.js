import esbuild from "esbuild";

await esbuild.build({
  entryPoints: ["src/indexBrowser.tsx"],
  bundle: true,
  outfile: "../extension/dist/indexBrowser.js",
  sourcemap: true,
  platform: "browser",
  loader: {
    ".json": "json",
    ".css": "css",
  },
  plugins: [],
  logLevel: "info",
  logLimit: 0,
});
