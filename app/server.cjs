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

let vscodeResponse = [];
let currentId = 1;

app.get('/indexBrowser.js', (req, res) => {
  res.set('Content-Type', 'application/javascript');
  res.sendFile(path.join(__dirname, "dist", "indexBrowser.js"));
});

app.post("/sendTypes", (req, res) => {
  vscodeResponse = req.body;
  currentId += 1;
  console.log("Recieved", vscodeResponse);
  res.send(`Recieved ${vscodeResponse}`);
});

app.get("/getTypes", (req, res) => {
  res.send({ ...vscodeResponse, id: currentId });
});

function getInlineHtmlWithJsTag(jsUrl) {
  const html = `
    <!DOCTYPE html>
    <html>
      <head>
        <meta charset="utf-8">
        <meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover" />
        <title>Paper proof</title>
      </head>
      <body>
        <div id="root"></div>
        <script src="${jsUrl}"></script>
      </body>
    </html>
  `;
  return html;
}

app.get("/", (req, res) => {
  const myJsUrl = "/indexBrowser.js";
  const myHtml = getInlineHtmlWithJsTag(myJsUrl);
  res.send(myHtml);
});
