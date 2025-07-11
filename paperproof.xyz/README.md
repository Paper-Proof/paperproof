# Paperproof Snapshot Server

A simple Express.js server that handles creating and serving Paperproof snapshots.

## Setup

1. Install dependencies:
```bash
npm install
```

2. Start the server:
```bash
npm start
```

For development with auto-restart:
```bash
npm run dev
```

## API Endpoints

- `POST /api/snapshot` - Create a new snapshot (expects HTML content in body)
- `GET /:id` - Retrieve a snapshot by ID
- `GET /api/health` - Health check

## Features

- Accepts HTML snapshots up to 10MB
- Generates random 16-character IDs for snapshots
- Stores snapshots as static HTML files
- CORS enabled for cross-origin requests

## Deployment

For production deployment, consider:

1. Using a process manager like PM2
2. Setting up a reverse proxy (nginx)
3. Adding rate limiting
4. Implementing cleanup for old snapshots
5. Using a proper domain name (paperproof.xyz)

## Environment Variables

- `PORT` - Server port (default: 3000)

Example production start:
```bash
PORT=80 npm start
```
