#!/bin/bash
# Ships code to an already-provisioned droplet. For a fresh one, use deploy.sh.
# Usage: ./push.sh [droplet_ip]
set -e

DROPLET=${1:-"128.199.52.81"}
APP=/var/www/paperproof.xyz
SITE=https://paperproof.xyz

cd "$(dirname "$0")/.."

# [Claude comment] The droplet installs with `npm ci --only=production`, so nothing is built there.
echo "📦 Building..."
npm run build

echo "📤 Uploading..."
scp server.js          root@$DROPLET:$APP/server.js
scp public/index.html  root@$DROPLET:$APP/public/index.html
scp public/dist/*      root@$DROPLET:$APP/public/dist/

echo "♻️  Restarting..."
ssh root@$DROPLET "cd $APP && chown -R www-data:www-data server.js public && \
  sudo -u www-data HOME=/home/www-data pm2 restart paperproof-server --update-env"

echo "🔍 Verifying..."
sleep 3
curl -fsS $SITE/api/health > /dev/null

for f in landingPage.js snapshotRenderer.js standaloneRenderer.js; do
  # [Claude comment] Nothing bumps a version number, so a stale asset is invisible unless compared.
  [ "$(md5sum public/dist/$f | cut -d' ' -f1)" = "$(curl -fsS $SITE/dist/$f | md5sum | cut -d' ' -f1)" ] \
    || { echo "❌ $f does not match what's live"; exit 1; }
done

echo "✅ Done - $SITE"
