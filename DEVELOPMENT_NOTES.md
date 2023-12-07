# Extension

1. I started
- enabling offline paperproof use, and
- removing our `server.cjs` to simplify development setup
however I stopped both for now - turns out using `server.cjs` is the fastest way to reload development code! (see https://github.com/microsoft/vscode/issues/190917 and https://code.visualstudio.com/api/get-started/your-first-extension - the fastest default way requires `Developer: Reload Window`!)

Either way, we still want offline paperproof, so see `[for paperproof:offline]` comments to pick that up.
