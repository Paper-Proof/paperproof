# paperproof.xyz

Landing page, `/playground`, and the snapshots the VSCode extension creates.

## Develop

```bash
npm install
npm run build      # bundles src/ into public/dist
npm run dev        # nodemon on :3001
```

`npm run build` (esbuild) is **required before deploying** — the droplet installs
with `npm ci --only=production` and esbuild is a devDependency, so nothing is
built server-side.

## Routes

| | |
|---|---|
| `/` | landing page (prerendered at build time into `public/dist/index.html`) |
| `/playground` | natural-language → proof tree editor |
| `/:id` | a snapshot |
| `POST /api/snapshot` | create one (10mb limit) |
| `POST /api/latex`, `/api/image-to-text-stream`, `/api/natural-to-proof-stream` | LLM proxies, keep the API keys server-side |
| `GET /api/health` | health check |

## Snapshots

Two formats live side by side in `./snapshots`, and `POST /api/snapshot` accepts
both — so extensions published before the JSON format keep working. **Deploy the
server before publishing an extension that sends the new format.**

- `<id>.json` — proof data. The page shell is generated per request, so a
  snapshot re-renders with whatever the current frontend is. Arrows get measured
  against the DOM on the reader's machine instead of being baked in.
- `<id>.html` — a frozen HTML dump from before that, with the stylesheet of the
  day inlined. Served byte-for-byte as it was built.

`./snapshots` is user data that exists **only on the droplet** — gitignored, and
excluded from the deploy archive. Never `rm -rf` the app directory; extract over it.

## Deploy

```bash
deployment/push.sh          # ship a code change
```

Builds, uploads `server.js` + `public/`, restarts pm2, and checks the live
bundles match what it just built. Never touches `snapshots/`.

`deployment/deploy.sh` is a different thing — it provisions a *fresh* droplet
(`apt upgrade -y`, reinstalls node/pm2/nginx/certbot). Don't use it to ship code.

On the droplet: app in `/var/www/paperproof.xyz` (pm2 app `paperproof-server`,
`cwd` pinned by `deployment/ecosystem.config.cjs` because `SNAPSHOTS_DIR` is
relative), logs in `/var/log/paperproof`, nginx config at
`/etc/nginx/sites-available/paperproof.xyz` (a plain reverse proxy to `:3001`),
certs under `/etc/letsencrypt/live/paperproof.xyz`.

## Environment

`.env`, not committed: `OPENAI_API_KEY`, `DEEPSEEK_API_KEY`, `PORT` (default 3001).
