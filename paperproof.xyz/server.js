// Very simple server for paperproof.xyz
const express = require('express');
const crypto = require('crypto');
const fs = require('fs').promises;
const path = require('path');
const cors = require('cors');

const app = express();

// Enhanced CORS configuration for Codespaces and other origins
app.use(cors({
  origin: true, // Allow all origins
  credentials: true,
  methods: ['GET', 'POST', 'PUT', 'DELETE', 'OPTIONS'],
  allowedHeaders: ['Content-Type', 'Authorization', 'X-Requested-With'],
  exposedHeaders: ['Content-Length', 'Content-Type']
}));

// Handle preflight requests explicitly
app.options('*', (req, res) => {
  res.header('Access-Control-Allow-Origin', '*');
  res.header('Access-Control-Allow-Methods', 'GET, POST, PUT, DELETE, OPTIONS');
  res.header('Access-Control-Allow-Headers', 'Content-Type, Authorization, X-Requested-With');
  res.sendStatus(200);
});

app.use(express.json({ limit: '10mb' }));

const SNAPSHOTS_DIR = './snapshots';

// Ensure directories exist
async function ensureDirectories() {
  try {
    await fs.access(SNAPSHOTS_DIR);
  } catch {
    await fs.mkdir(SNAPSHOTS_DIR, { recursive: true });
  }
}

// Load CSS
async function loadCSS() {
  try {
    const cssPath = './public/dist/standaloneRenderer.css';
    const css = await fs.readFile(cssPath, 'utf8');
    return css;
  } catch (error) {
    console.error('Error loading CSS:', error);
    return '';
  }
}

// Generate complete HTML with CSS
// Generate complete HTML with CSS
function generateSnapshotHTML(proofTreeHTML, css) {
  return `<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>Snapshot</title>
  
  <!-- Favicon -->
  <link rel="apple-touch-icon" sizes="180x180" href="/apple-touch-icon.png">
  <link rel="icon" type="image/png" sizes="32x32" href="/favicon-32x32.png">
  <link rel="icon" type="image/png" sizes="16x16" href="/favicon-16x16.png">
  <link rel="manifest" href="/site.webmanifest">
  
  <style>
  @import url('https://fonts.googleapis.com/css2?family=Roboto+Mono:ital,wght@0,100..700;1,100..700&display=swap');
  </style>
  <style>
    ${css}
  </style>
</head>
<body class="snapshot">
  ${proofTreeHTML}
</body>
</html>`;
}

// Create snapshot
app.post('/api/snapshot', async (req, res) => {
  try {
    await ensureDirectories();
    
    const { proofTreeHTML } = req.body;
    
    if (!proofTreeHTML) {
      return res.status(400).json({ error: 'Missing proofTreeHTML' });
    }
    
    const css = await loadCSS();
    const completeHTML = generateSnapshotHTML(proofTreeHTML, css);
    
    const id = crypto.randomBytes(8).toString('hex');
    const filePath = path.join(SNAPSHOTS_DIR, `${id}.html`);
    
    await fs.writeFile(filePath, completeHTML);
    
    console.log(`Created snapshot: ${id}`);
    res.json({ id });
  } catch (error) {
    console.error('Failed to create snapshot:', error);
    res.status(500).json({ error: 'Failed to create snapshot' });
  }
});

// Serve the built JavaScript file
app.get('/dist/standaloneRenderer.js', async (req, res) => {
  try {
    const jsPath = './public/dist/standaloneRenderer.js';
    const js = await fs.readFile(jsPath, 'utf8');
    res.setHeader('Content-Type', 'application/javascript');
    res.send(js);
  } catch (error) {
    console.error('Error serving renderer JS:', error);
    res.status(500).send('Error loading renderer JS');
  }
});

// Serve the built CSS file
app.get('/dist/standaloneRenderer.css', async (req, res) => {
  try {
    const cssPath = './public/dist/standaloneRenderer.css';
    const css = await fs.readFile(cssPath, 'utf8');
    res.setHeader('Content-Type', 'text/css');
    res.send(css);
  } catch (error) {
    console.error('Error serving renderer CSS:', error);
    res.status(500).send('Error loading renderer CSS');
  }
});

// Standalone renderer page - serve the built HTML
app.get('/', async (req, res) => {
  try {
    const htmlPath = './public/standalone-renderer.html';
    const html = await fs.readFile(htmlPath, 'utf8');
    res.send(html);
  } catch (error) {
    console.error('Error serving renderer page:', error);
    res.status(500).send('Error loading renderer page');
  }
});

// Serve favicon files
app.get('/favicon.ico', (req, res) => {
  res.sendFile(path.join(__dirname, 'assets/favicon/favicon.ico'));
});

app.get('/favicon-16x16.png', (req, res) => {
  res.sendFile(path.join(__dirname, 'assets/favicon/favicon-16x16.png'));
});

app.get('/favicon-32x32.png', (req, res) => {
  res.sendFile(path.join(__dirname, 'assets/favicon/favicon-32x32.png'));
});

app.get('/apple-touch-icon.png', (req, res) => {
  res.sendFile(path.join(__dirname, 'assets/favicon/apple-touch-icon.png'));
});

app.get('/android-chrome-192x192.png', (req, res) => {
  res.sendFile(path.join(__dirname, 'assets/favicon/android-chrome-192x192.png'));
});

app.get('/android-chrome-512x512.png', (req, res) => {
  res.sendFile(path.join(__dirname, 'assets/favicon/android-chrome-512x512.png'));
});

app.get('/site.webmanifest', (req, res) => {
  res.sendFile(path.join(__dirname, 'assets/favicon/site.webmanifest'));
});

// Health check
app.get('/api/health', (req, res) => {
  res.json({ status: 'ok' });
});


// Serve snapshot
app.get('/:id', async (req, res) => {
  try {
    const filePath = path.join(SNAPSHOTS_DIR, `${req.params.id}.html`); // FIXED: was just `${id}.html`
    const html = await fs.readFile(filePath, 'utf8');
    res.send(html);
  } catch (error) {
    console.error('Snapshot not found:', req.params.id);
    res.status(404).send('Snapshot not found');
  }
});


const PORT = process.env.PORT || 3001;
app.listen(PORT, () => {
  console.log(`Paperproof snapshot server running on port ${PORT}`);
});
