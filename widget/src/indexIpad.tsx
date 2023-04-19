import * as React from "react";
import * as ReactDOM from "react-dom";
import App from "./tldraw_stuff/App";

// Hah, learned what to do. The problem was that I was `export default function`.
// Of course normal <script/> doesn't understand that!
ReactDOM.render(
  <React.StrictMode>
    <h1>MMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMM</h1>
    <h2>And some new stufff!</h2>
    <App/>
  </React.StrictMode>,
  document.getElementById('root')
)
