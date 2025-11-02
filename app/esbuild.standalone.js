import esbuild from "esbuild";
import path from "path";
import { fileURLToPath } from "url";

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

// Plugin to alias indexBrowser imports
const aliasPlugin = {
  name: 'alias',
  setup(build) {
    build.onResolve({ filter: /^src\/indexBrowser$/ }, args => {
      return { path: path.resolve(__dirname, 'src/standaloneRenderer.tsx') }
    })
  },
}

await esbuild.build({
  entryPoints: ["src/standaloneRenderer.tsx"],
  bundle: true,
  outfile: "dist/standaloneRenderer.js",
  sourcemap: true,
  platform: "browser",
  loader: {
    ".json": "json",
    ".css": "css",
  },
  plugins: [aliasPlugin],
  logLevel: "info",
  logLimit: 0,
  define: {
    "process.env.NODE_ENV": '"production"',
  },
  minify: false, // Keep unminified for easier debugging
  external: ['stream', 'zlib', 'url', 'http', 'events', 'crypto', 'tls', 'https', 'net', 'buffer', 'os', 'path', 'fs'],
});

console.log("Standalone renderer built successfully!");