import esbuild from "esbuild";

let ctx = await esbuild.context({
  entryPoints: ["src/indexBrowser.tsx"],
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
});

await ctx.watch();
