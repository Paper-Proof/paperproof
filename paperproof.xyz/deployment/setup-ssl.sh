#!/bin/bash

# 🔒 SSL Certificate Setup for Paperproof.xyz
# Run this after your domain DNS is properly configured

DROPLET_IP=${1:-"128.199.52.81"}
DOMAIN="paperproof.xyz"

echo "🔒 Setting up SSL certificate..."

ssh root@$DROPLET_IP << EOF
# Get SSL certificate
certbot --nginx -d $DOMAIN \
    --non-interactive --agree-tos --email admin@$DOMAIN

# Restart nginx
systemctl restart nginx

echo "✅ SSL certificate installed"
EOF

echo "✨ SSL setup complete!"
echo "Your server is now secure at:"
echo "  🔒 https://$DOMAIN"
