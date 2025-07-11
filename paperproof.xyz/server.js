// Very simple server for paperproof.xyz
const express = require('express');
const crypto = require('crypto');
const fs = require('fs').promises;
const path = require('path');
const cors = require('cors');

const app = express();
app.use(cors());
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
    const cssPath = '../app/src/index.css'; // Path to your main CSS file
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
  <title>Paperproof Snapshot</title>
  
  <style>
@import url('https://fonts.googleapis.com/css2?family=Roboto+Mono:ital,wght@0,100..700;1,100..700&display=swap');
</style>
  <style>
  
    ${css}

    /* Snapshot-specific overrides */
    .proof-tree {
      transform: none !important;
    }
    
    /* Disable interactive elements in snapshot */
    button { pointer-events: none; }
    .MuiMenu-root { display: none !important; }
    

    body{
    font-family: monospace;
      --vscode-editor-font-family: monospace;
      padding: 0 !important;
    }
      *{
    font-family: monospace !important;
    }
  </style>
</head>
<body>
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

// Health check
app.get('/api/health', (req, res) => {
  res.json({ status: 'ok' });
});

const PORT = process.env.PORT || 3001;
app.listen(PORT, () => {
  console.log(`Paperproof snapshot server running on port ${PORT}`);
});