const express = require('express')
const bodyParser = require('body-parser');
const cors = require('cors');
const path = require('path');

const app = express()
const port = 3000


// Serve static files from the 'widget/dist' directory
app.use("/", express.static(path.join(__dirname, "dist")));
// For source maps
app.use("/src", express.static(path.join(__dirname, "src")));

const allowedOrigins = ["localhost:5431"];
app.use(
  cors({
    origin: function (origin, callback) {
      return callback(null, true);
      /*if (!origin) return callback(null, true);
    if (allowedOrigins.indexOf(origin) === -1) {
      const msg = 'The CORS policy for this site does not allow access from the specified Origin.';
      return callback(new Error(msg), false);
    }
    return callback(null, true);*/
    },
  })
);

app.use(bodyParser.json());

let hyps = [];
let curId = 1;

app.post("/sendTypes", (req, res) => {
  const data = req.body;
  hyps = { data, id: curId++ };
  console.log("Recieved", data);
  res.send(`Recieved ${data}`);
});

app.get("/getTypes", (req, res) => {
  res.send(hyps);
});

function getInlineHtmlWithJsTag(jsUrl) {
  const html = `
    <!DOCTYPE html>
    <html>
      <head>
        <meta charset="utf-8">
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

app.listen(port, () => {
  console.log(`Example app listening on port ${port}`)
})