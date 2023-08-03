import { nodeResolve } from "@rollup/plugin-node-resolve";
import typescript from "@rollup/plugin-typescript";
import commonjs from "@rollup/plugin-commonjs";
import replace from "@rollup/plugin-replace";
import json from "@rollup/plugin-json";
import postcss from "rollup-plugin-postcss";
import path from "path";
// PSA: would be super nice to have the notification plugin work,
// BUT we'd need to change `typescript` to `babel` like here
// (https://stackoverflow.com/a/76278565/3192470)
//
// import notify from 'rollup-plugin-notify';

const plugins = [
  // TODO we don't actually use postcss? Do we?
  postcss({}),
  typescript({
    tsconfig: "./tsconfig.json",
    outputToFilesystem: false,
    sourceMap: true,
  }),
  json(),
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
  return [
    {
      input: `src/indexBrowser.tsx`,
      output: {
        file: "dist/indexBrowser.js",
        format: "iife",
        // Hax: apparently setting `global` makes some CommonJS modules work ¯\_(ツ)_/¯
        intro: "const global = window",
        sourcemap: true,
      },
      plugins,
      // Remove safe (supposedly!) warnings,
      // copypasted from (https://stackoverflow.com/a/43556986/3192470)
      onwarn: function (warning, handler) {
        // Skip certain warnings

        // This is for @supabase package
        if (warning.code === 'THIS_IS_UNDEFINED') { return; }

        // This is for @tldraw package
        if (warning.code === 'CIRCULAR_DEPENDENCY') { return; }

        // console.warn everything else
        handler(warning);
      }
    },
  ];
};
