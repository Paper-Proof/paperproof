# tactictree README

Tactic Tree extension allows to visualize Lean 4 tactic proofs on the canvas.
As you edit the proof, the state is sent to the server via the extension and rendered in the browser.

## Features

Command `Tactic Tree : Toggle` toggles the tactic tree view.

## Requirements

You need to:
- have Lean 4 extension installed
- import PaperProof.lean from your file
- run the server with `node server.cjs` in the widget/app folder

## Known Issues

In the future running the local server will not be required (either vscode extension will server
or the server will be hosted somewhere). Hopefully PaperProof package defining the
server function for the Lean language server would be somehow linked automatically by extension.

## Release Notes

### 0.0.1

Initial release of the extension sending data to the server.

### 0.0.4

Send state updates directly to extension webview as well as the server

### 0.0.5

Support sessions