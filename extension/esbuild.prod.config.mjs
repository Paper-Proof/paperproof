import esbuild from "esbuild";

await esbuild.build({
  entryPoints: ["../app/src/indexBrowser.tsx"],
  bundle: true,
  outfile: "dist/indexBrowser.js",
  sourcemap: true,
  platform: "browser",
  loader: {
    ".json": "json",
    ".css": "css",
  },
  plugins: [],
  logLevel: "info",
  logLimit: 0,
  define: {
    "process.env.NODE_ENV": '"production"',
  },
  minify: true,
});
