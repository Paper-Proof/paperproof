// 📚 PM2 Configuration for Paperproof

module.exports = {
  apps: [{
    name: 'paperproof-server',
    script: 'server.js',
    cwd: '/var/www/paperproof.xyz',
    instances: 1,
    autorestart: true,
    watch: false,
    max_memory_restart: '1G',
    env: {
      NODE_ENV: 'production',
      PORT: 3001
    },
    error_file: '/var/log/paperproof/err.log',
    out_file: '/var/log/paperproof/out.log',
    log_file: '/var/log/paperproof/combined.log',
    time: true
  }]
};