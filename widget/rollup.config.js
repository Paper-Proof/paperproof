import { nodeResolve } from "@rollup/plugin-node-resolve";
import typescript from "@rollup/plugin-typescript";
import commonjs from "@rollup/plugin-commonjs";
import replace from "@rollup/plugin-replace";
import path from "path";

const plugins = [
  typescript({
    tsconfig: "./tsconfig.json",
    outputToFilesystem: false,
    sourceMap: true,
  }),
  nodeResolve({
    browser: true,
    modulePaths: [path.resolve(__dirname, "node_modules")],
  }),
  replace({
    "typeof window": JSON.stringify("object"),
    "process.env.NODE_ENV": JSON.stringify(process.env.NODE_ENV),
    preventAssignment: true, // TODO delete when `true` becomes the default
  }),
  commonjs({
    // In some cases the common.js plugin will hoist dynamic `require` calls for Node.js
    // modules which are not ever actually called into a global `import` which we cannot
    // resolve since we are running in a browser. So block all these from being hoisted.
    // Note: one alternative, https://github.com/FredKSchott/rollup-plugin-polyfill-node
    // does not seem to work.
    ignore: [
      "process",
      "events",
      "stream",
      "util",
      "path",
      "buffer",
      "querystring",
      "url",
      "string_decoder",
      "punycode",
      "http",
      "https",
      "os",
      "assert",
      "constants",
      "timers",
      "console",
      "vm",
      "zlib",
      "tty",
      "domain",
      "dns",
      "dgram",
      "child_process",
      "cluster",
      "module",
      "net",
      "readline",
      "repl",
      "tls",
      "fs",
      "crypto",
      "perf_hooks",
    ],
  }),
];

export default (cliArgs) => {
  // lakesare: We're compiling our tldraw code for browser & vscode's extension separately, because:
  // - vscode expects our code to be a module ({ format: "es" }, https://developer.mozilla.org/en-US/docs/Web/JavaScript/Guide/Modules#javascript.statements.import)
  // - we could add it to the browser app via `<script type="module"/>`, but that would require externalizing ["react", "react-dom", "@leanprover/infoview"] somehow and I didn't want to google how to set this up. ALSO we would want 2 separate source files either way - one for browser, `indexBrowser.tsx` (that mounts the react component to out localhost:3000 html page); and one for the vscode extension, `indexExtension.tsx` (that just exports the react component). ALSO - sourcemaps, as described below!

  if (cliArgs.configBrowser) {
    return [
      {
        input: `src/indexBrowser.tsx`, 
        output: {
          file: 'dist/indexBrowser.js',
          format: 'iife',
          // Hax: apparently setting `global` makes some CommonJS modules work ¯\_(ツ)_/¯
          intro: "const global = window",
          sourcemap: true,
        },
        plugins
      },
      {
        input: `src/extensionAsApi.tsx`,
        output: {
          file: 'dist/extensionAsApi.js',
          format: "es",
          intro: "const global = window",
          sourcemap: false,
        },
        external: ["react", "react-dom", "@leanprover/infoview"],
        plugins
      },
    ]
  } else {
    return {
      input: [`src/indexExtension.tsx`],
      output: {
        dir: "dist",
        format: "es",
        intro: "const global = window",
        // !!! Enabling sourcemaps in the extension code leads to the mysterious `Error: Failed to construct 'URL': Invalid URL`, beware!
        // If you like sourcemaps just develop in the browser.
        sourcemap: false,
      },
      external: ["react", "react-dom", "@leanprover/infoview"],
      plugins,
    };
  }
};
