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
  define: {
    "process.env.NODE_ENV": '"production"',
  },
  minify: true,
  external: ['stream', 'zlib', 'url', 'http', 'events', 'crypto', 'tls', 'https', 'net', 'buffer', 'os', 'path', 'fs'],
});
