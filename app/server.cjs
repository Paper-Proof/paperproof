const express = require('express')
const bodyParser = require('body-parser');
const cors = require('cors');
const path = require('path');
const fs = require('fs');
const http = require('http');
const https = require('https');

const app = express()
http.createServer(app).listen(80, () => {
  console.log(`Listening on port 80`)
});

let withHttps = false;
// Middleware to redirect from http to https
app.use((req, res, next) => {
  if (!withHttps || req.secure) {
    next();
  } else {
    res.redirect(301, `https://${req.headers.host}${req.url}`);
  }
});
 
try {
  const options = {
    cert: fs.readFileSync('/etc/letsencrypt/live/paperproof.xyz/fullchain.pem'),
    key: fs.readFileSync('/etc/letsencrypt/live/paperproof.xyz/privkey.pem')
  };
  https.createServer(options, app).listen(443, () => {
    console.log('HTTPS server is running on port 443')
    withHttps = true;
 });
} catch (e) {
  console.log('Error starting https server', e);
}

// Serve static files from the 'app/dist' directory
app.use("/", express.static(path.join(__dirname, "dist")));
// For source maps
app.use("/src", express.static(path.join(__dirname, "src")));

app.use(
  cors({
    origin: function (origin, callback) {
      return callback(null, true);
    },
  })
);

app.use(bodyParser.json({ limit: "50mb" }));

// TODO: Move to persistent database.
// Database of saved information for each session, keyed by sessionId.
const db = new Map();

app.get("/indexBrowser.js", (req, res) => {
  res.set("Content-Type", "application/javascript");
  res.sendFile(path.join(__dirname, "dist", "indexBrowser.js"));
});

let sessionId = 0;

app.post("/newSession", (req, res) => {
  sessionId += 1;
  console.log("New session", sessionId);
  res.send({ sessionId });
});

app.post("/sendTypes", (req, res) => {
  const sessionId = req.query.sessionId;
  const { id } = db.get(sessionId) || { id: 0 };
  db.set(sessionId, { id: id + 1, types: req.body });
  console.log("Recieved for session: ", sessionId, req.body);
  res.send("OK");
});

app.get("/getTypes", (req, res) => {
  const sessionId = req.query.sessionId;
  const { id, types } = db.get(sessionId) || { id: 0, types: {} };
  console.log("Get for session: ", sessionId, types);
  res.send({ ...types, id });
});

function getInlineHtmlWithJsTag(jsUrl, sessionId) {
  const html = `
    <!DOCTYPE html>
    <html>
      <head>
        <meta charset="utf-8">
        <meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover" />
        <title>Paperproof</title>
      </head>
      <body>
        <script>sessionId = ${sessionId}</script>
        <div id="root"></div>
        <script src="${jsUrl}"></script>
      </body>
    </html>
  `;
  return html;
}

app.get("/:sessionId", (req, res) => {
  const myJsUrl = "/indexBrowser.js";
  const myHtml = getInlineHtmlWithJsTag(myJsUrl, req.params.sessionId);
  res.send(myHtml);
});
