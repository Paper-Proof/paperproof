import esbuild from 'esbuild';
import path from 'path';

let ctx = await esbuild.context({
  entryPoints: ['src/indexBrowser.tsx'],
  bundle: true,
  // [For paperproof:offline]
  // outfile: '../extension/dist/indexBrowser.js',
  outfile: 'dist/indexBrowser.js',
  sourcemap: true,
  platform: 'browser',
  loader: {
    '.json': 'json',
    '.css': 'css',
  },
  plugins: [],
  logLevel: 'info',
  logLimit: 0,
})

await ctx.watch()
