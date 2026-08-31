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

`deployment/deploy.sh` provisions a *fresh* droplet: it runs `apt upgrade -y` and
reinstalls node/pm2/nginx/certbot. Don't use it to ship a code change.

For a code change, build locally and copy only what moved:

```bash
npm run build
scp server.js public/dist/* root@<ip>:/var/www/paperproof.xyz/...   # mind the two dirs
ssh root@<ip> 'cd /var/www/paperproof.xyz && chown -R www-data:www-data server.js public/dist && \
  sudo -u www-data HOME=/home/www-data pm2 restart paperproof-server --update-env'
```

Static assets need no restart; only `server.js` does. Back up what you replace
first — there's no git checkout on the droplet.

On the droplet: app in `/var/www/paperproof.xyz` (pm2 app `paperproof-server`,
`cwd` pinned by `deployment/ecosystem.config.cjs` because `SNAPSHOTS_DIR` is
relative), logs in `/var/log/paperproof`, nginx config at
`/etc/nginx/sites-available/paperproof.xyz` (a plain reverse proxy to `:3001`),
certs under `/etc/letsencrypt/live/paperproof.xyz`.

## Environment

`.env`, not committed: `OPENAI_API_KEY`, `DEEPSEEK_API_KEY`, `PORT` (default 3001).
