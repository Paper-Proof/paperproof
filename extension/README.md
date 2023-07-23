# Paper Proof

Paper Proof extension allows to visualize Lean 4 tactic proofs on the canvas.
As you edit the proof, the state is sent to the server via the extension and can be
viewed in the webview or the browser.

## Features

Command `Paper Proof : Toggle` toggles the paper proof view.

## Requirements

You need to:
- have Lean 4 extension installed
- import PaperProof.lean from your file

## Known Issues

Instead of requiring to import PaperProof.lean which defines custom RPC method it
would be nice to make extension handle it somehow automatically.

## Release Notes

### 0.0.1

Initial release of the extension sending data to the server.

### 0.0.4

Send state updates directly to extension webview as well as the server

### 0.0.5

Support sessions. Also the server URL can be configured in settings: http://localhost:80 or https://paperproof.xyz.

### 0.0.6

Use supabase