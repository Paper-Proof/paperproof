import esbuild from 'esbuild';
import path from 'path';

let ctx = await esbuild.context({
  entryPoints: ['src/indexBrowser.tsx'],
  bundle: true,
  outfile: 'dist/indexBrowser.js',
  sourcemap: true,
  platform: 'browser',
  loader: {
    '.json': 'json',
    '.css': 'css',
  },
  plugins: [
    // TODO: Add necessary plugins here
  ],
  logLevel: 'info',
  logLimit: 0,
})

await ctx.watch()
