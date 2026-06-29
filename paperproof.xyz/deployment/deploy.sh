#!/bin/bash

# 📚 Paperproof.xyz Deployment Script
# Usage: ./deploy.sh [droplet_ip]

set -e

DROPLET_IP=${1:-"128.199.52.81"}
DOMAIN="paperproof.xyz"
APP_DIR="/var/www/paperproof.xyz"

echo "📚 Starting paperproof.xyz deployment to $DROPLET_IP"

echo "📦 Creating deployment archive..."
cd ..
tar -czf deployment/paperproof-deploy.tar.gz \
    --exclude='node_modules' \
    --exclude='.git' \
    --exclude='*.log' \
    --exclude='snapshots' \
    --exclude='deployment/paperproof-deploy.tar.gz' \
    .

echo "🔧 Setting up server dependencies..."
ssh root@$DROPLET_IP << 'EOF'
    # Update system
    apt update && apt upgrade -y
    
    # Install Node.js
    curl -fsSL https://deb.nodesource.com/setup_18.x | bash -
    apt-get install -y nodejs
    
    # Install PM2, nginx, and certbot
    npm install -g pm2
    apt-get install -y nginx certbot python3-certbot-nginx
    
    # Create directories
    mkdir -p /var/www/paperproof.xyz /var/log/paperproof
    
    echo "✅ Server setup complete"
EOF

echo "📤 Uploading application..."
scp deployment/paperproof-deploy.tar.gz root@$DROPLET_IP:/tmp/

echo "⚙️ Installing application..."
ssh root@$DROPLET_IP << 'EOF'
    cd /var/www/paperproof.xyz
    tar -xzf /tmp/paperproof-deploy.tar.gz --strip-components=1
    npm ci --only=production
    chown -R www-data:www-data /var/www/paperproof.xyz /var/log/paperproof
    echo "✅ Application installed"
EOF

echo "🌐 Configuring nginx..."
ssh root@$DROPLET_IP << 'EOF'
    cp /var/www/paperproof.xyz/deployment/nginx.conf /etc/nginx/sites-available/paperproof.xyz
    ln -sf /etc/nginx/sites-available/paperproof.xyz /etc/nginx/sites-enabled/
    rm -f /etc/nginx/sites-enabled/default
    nginx -t && systemctl reload nginx
    echo "✅ Nginx configured"
EOF

echo "⚙️ Starting application..."
ssh root@$DROPLET_IP << 'EOF'
    cd /var/www/paperproof.xyz
    mkdir -p /home/www-data/.pm2
    chown -R www-data:www-data /home/www-data/.pm2
    sudo -u www-data HOME=/home/www-data pm2 startOrRestart deployment/ecosystem.config.cjs --update-env
    sudo -u www-data HOME=/home/www-data pm2 save
    pm2 startup systemd -u www-data --hp /home/www-data
    systemctl enable nginx
    echo "✅ Application started"
EOF

echo "🧹 Cleaning up..."
rm deployment/paperproof-deploy.tar.gz

echo "🎉 Paperproof.xyz deployment complete!"
echo ""
echo "Your server is now running at:"
echo "  📍 http://$DROPLET_IP"
echo ""
echo "Management commands:"
echo "  📊 ssh root@$DROPLET_IP 'sudo -u www-data HOME=/home/www-data pm2 status'"
echo "  📝 ssh root@$DROPLET_IP 'sudo -u www-data HOME=/home/www-data pm2 logs paperproof-server'"
