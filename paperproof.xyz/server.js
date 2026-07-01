// Very simple server for paperproof.xyz
try {
  const { readFileSync } = await import('fs');
  const envPath = new URL('.env', import.meta.url).pathname;
  for (const line of readFileSync(envPath, 'utf8').split('\n')) {
    const m = line.match(/^([^#=]+)=(.*)$/);
    if (m) process.env[m[1].trim()] = m[2].trim();
  }
} catch {}
import express from 'express';
import crypto from 'crypto';
import { promises as fs } from 'fs';
import path from 'path';
import cors from 'cors';
import { fileURLToPath } from 'url';
import { Readable } from 'stream';
import { llmInstructions, fewShotExamples } from './src/services/llmInstructions.js';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

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
app.use(express.static(path.join(__dirname, 'public')));

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

app.get('/playground', (req, res) => {
  res.sendFile(path.join(__dirname, 'public', 'playground.html'));
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

// Streaming image → text extraction (OpenAI gpt-4o, vision-capable)
app.post('/api/image-to-text-stream', async (req, res) => {
  const apiKey = process.env.OPENAI_API_KEY;
  if (!apiKey) return res.status(500).json({ error: 'OPENAI_API_KEY not configured on server' });

  const { imageDataUrl, additionalText } = req.body;
  if (!imageDataUrl) return res.status(400).json({ error: 'imageDataUrl is required' });

  const userContent = [
    { type: 'image_url', image_url: { url: imageDataUrl } },
    { type: 'text', text:
      `
        This is an image with a proof of a mathematical theorem. Please turn this image into text. For mathematical symbols, use unicode.
        Write
        STATEMENT: ...
        PROOF: ...
        Preserve all mathematical notation exactly. Return only the theorem statement and proof text, no commentary please.
        ${additionalText ? "Additional context from the user:" + additionalText : ""}
      `
    }
  ];

  try {
    const response = await fetch('https://api.openai.com/v1/chat/completions', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json', 'Authorization': `Bearer ${apiKey}` },
      body: JSON.stringify({
        model: 'gpt-4o',
        stream: true,
        messages: [{ role: 'user', content: userContent }],
      }),
    });

    if (!response.ok) {
      const data = await response.json();
      return res.status(response.status).json(data);
    }

    res.setHeader('Content-Type', 'text/event-stream');
    res.setHeader('Cache-Control', 'no-cache');
    res.setHeader('Connection', 'keep-alive');
    Readable.fromWeb(response.body).pipe(res);
  } catch (error) {
    console.error('image-to-text-stream error:', error);
    if (!res.headersSent) res.status(500).json({ error: 'Failed to contact OpenAI' });
  }
});

function buildMessages(proof, previousAttempt) {
  const messages = [
    { role: 'system', content: llmInstructions },
  ];
  for (const example of fewShotExamples) {
    messages.push({ role: 'user', content: example.text });
    messages.push({ role: 'assistant', content: example.json });
  }
  messages.push({ role: 'user', content: proof });
  if (previousAttempt?.json && previousAttempt?.error) {
    messages.push({ role: 'assistant', content: previousAttempt.json });
    messages.push({ role: 'user', content: `The JSON you produced has this error: ${previousAttempt.error}\n\nPlease fix it and return the corrected JSON only.` });
  }
  return messages;
}

// Pipes DeepSeek SSE directly to the client
app.post('/api/natural-to-proof-stream', async (req, res) => {
  const apiKey = process.env.DEEPSEEK_API_KEY;
  if (!apiKey) return res.status(500).json({ error: 'DEEPSEEK_API_KEY not configured on server' });

  const { proof, previousAttempt } = req.body;
  if (!proof?.trim()) return res.status(400).json({ error: 'proof is required' });

  const messages = buildMessages(proof, previousAttempt);

  try {
    const response = await fetch('https://api.deepseek.com/v1/chat/completions', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json', 'Authorization': `Bearer ${apiKey}` },
      body: JSON.stringify({
        model: 'deepseek-v4-flash',
        thinking: { type: 'enabled' },
        stream: true,
        messages,
      }),
    });

    if (!response.ok) {
      const data = await response.json();
      return res.status(response.status).json(data);
    }

    res.setHeader('Content-Type', 'text/event-stream');
    res.setHeader('Cache-Control', 'no-cache');
    res.setHeader('Connection', 'keep-alive');
    Readable.fromWeb(response.body).pipe(res);
  } catch (error) {
    console.error('natural-to-proof-stream error:', error);
    if (!res.headersSent) res.status(500).json({ error: 'Failed to contact DeepSeek' });
  }
});

// LaTeX conversion proxy — keeps the OpenAI key server-side
app.post('/api/latex', async (req, res) => {
  const apiKey = process.env.OPENAI_API_KEY;
  if (!apiKey) {
    return res.status(500).json({ error: 'OPENAI_API_KEY not configured on server' });
  }

  try {
    const response = await fetch('https://api.openai.com/v1/chat/completions', {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
        'Authorization': `Bearer ${apiKey}`,
      },
      body: JSON.stringify(req.body),
    });

    const data = await response.json();
    if (!response.ok) {
      return res.status(response.status).json(data);
    }
    res.json(data);
  } catch (error) {
    console.error('LaTeX proxy error:', error);
    res.status(500).json({ error: 'Failed to contact OpenAI' });
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


const PORT = process.env.PORT || 3001;
app.listen(PORT, () => {
  console.log(`Paperproof snapshot server running on port ${PORT}`);
});
