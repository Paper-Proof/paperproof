// ___Why do we need `cerver.cjs`, can't we simply server assets from within /extension?
//    We absolutely can, and that would simplify the development setup, however turns out using `server.cjs` is the fastest way to reload development code - the fastest default way requires `Developer: Reload Window` (see https://github.com/microsoft/vscode/issues/190917 and https://code.visualstudio.com/api/get-started/your-first-extension).
const express = require('express')
const path = require('path');
const http = require('http');

const app = express();
http.createServer(app).listen(80, () => {
  console.log("Listening on port 80...")
});

// Serve static files from the '/extension/dist' directory
app.use("/", express.static(path.join(__dirname, "..", "extension", "dist")));
