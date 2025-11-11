#!/bin/bash

# 📚 Paperproof.xyz Deployment Script
# Usage: ./deploy.sh [droplet_ip]

set -e

DROPLET_IP=${1:-"YOUR_DROPLET_IP"}
DOMAIN="paperproof.xyz"
APP_DIR="/var/www/paperproof.xyz"

echo "📚 Starting paperproof.xyz deployment to $DROPLET_IP"

# Check if we have the droplet IP
if [ "$DROPLET_IP" = "YOUR_DROPLET_IP" ]; then
    echo "❌ Please provide the droplet IP as first argument: ./deploy.sh <droplet_ip>"
    exit 1
fi

echo "📦 Creating deployment archive..."
cd ../..
tar -czf paperproof.xyz/deployment/paperproof-deploy.tar.gz \
    --exclude='node_modules' \
    --exclude='.git' \
    --exclude='*.log' \
    --exclude='snapshots' \
    --exclude='deployment' \
    --exclude='extension' \
    --exclude='lean' \
    --exclude='_examples' \
    --exclude='**/.lake' \
    --exclude='**/lake-packages' \
    --exclude='**/.yarn' \
    paperproof.xyz/ \
    app/dist/ \
    app/standalone-renderer.html

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
    mkdir -p /var/www/paperproof.xyz /var/log/paperproof /var/www/app
    
    echo "✅ Server setup complete"
EOF

echo "📤 Uploading application..."
scp paperproof.xyz/deployment/paperproof-deploy.tar.gz root@$DROPLET_IP:/tmp/

echo "⚙️ Installing application..."
ssh root@$DROPLET_IP << 'EOF'
    cd /var/www
    tar -xzf /tmp/paperproof-deploy.tar.gz
    cd paperproof.xyz
    npm ci --only=production
    chown -R www-data:www-data /var/www/paperproof.xyz /var/log/paperproof /var/www/app
    echo "✅ Application installed"
EOF

echo "🌐 Configuring nginx..."
ssh root@$DROPLET_IP << 'EOF'
    cp /var/www/paperproof.xyz/deployment/nginx.conf /etc/nginx/sites-available/paperproof.xyz
    ln -sf /etc/nginx/sites-available/paperproof.xyz /etc/nginx/sites-enabled/
    rm -f /etc/nginx/sites-enabled/default
    nginx -t && systemctl restart nginx
    echo "✅ Nginx configured"
EOF

echo "⚙️ Starting application..."
ssh root@$DROPLET_IP << 'EOF'
    cd /var/www/paperproof.xyz
    mkdir -p /home/www-data/.pm2
    chown -R www-data:www-data /home/www-data/.pm2
    sudo -u www-data HOME=/home/www-data pm2 start deployment/ecosystem.config.js
    sudo -u www-data HOME=/home/www-data pm2 save
    pm2 startup systemd -u www-data --hp /home/www-data
    systemctl enable nginx
    echo "✅ Application started"
EOF

echo "🧹 Cleaning up..."
rm paperproof.xyz/deployment/paperproof-deploy.tar.gz

echo "🎉 Paperproof.xyz deployment complete!"
echo ""
echo "Your server is now running at:"
echo "  📍 http://$DROPLET_IP"
echo ""
echo "Management commands:"
echo "  📊 ssh root@$DROPLET_IP 'sudo -u www-data HOME=/home/www-data pm2 status'"
echo "  📝 ssh root@$DROPLET_IP 'sudo -u www-data HOME=/home/www-data pm2 logs paperproof-server'"
