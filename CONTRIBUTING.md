## Developement

1. Install the extension from `extension/` folder
```console
code --install-extension paperproof-0.0.1.vsix
```

2. Run the dev server (you might need to run `yarn install` first)
```console
cd app; yarn dev
```

3. Toggle the view with `"Paperproof: Toggle"` command (Ctrl+Shift+P) or open in browser
from vscode status bar

### Reload 

If you change something in the `/extension` folder, run

```console
vsce package; code --uninstall-extension undefined_publisher.paperproof; code --install-extension paperproof-0.0.1.vsix
```
and quit VSCode.

On some changes, running `"Paperproof: Toggle"` is important.

### Publishing

Deploying our `main` branch consists of 3 steps - deploying to paperproof.xyz, publishing a new vscode extension, and publishing a new Paperproof Lean library.

#### Deploying /app

To deploy [paperproof.xyz](paperproof.xyz) contents:

1. Go to https://github.com/Paper-Proof/paperproof/actions/workflows/deploy-do.yml
2. Run the "Deploy to Digital Ocean" workflow

#### Deploying /extension

To deploy a vscode Paperproof extension:

1. Login into vsce
```
vsce login paperproof
```

You will need the Personal Access Token for the paperproof organisation to do this (please ask Evgenia or Anton if you need access).

2. Build and publish

```shell
vsce publish
```

#### Deploying /lean

To publish a new Paperproof Lean library, we just push to [github.com/Paper-Proof/paperproof](github.com/Paper-Proof/paperproof) `main` branch, the changes will be picked up automatically.

### Code structure

- `lean/` - defines the custom Lean server method which parses the InfoTree into appropriate format for visualization.
- `app/` - contains a simple server and the browser app which renders
the proof tree.
- `extension/` - contains the VSCode extension which queries the Lean server method defined in `lean/` each time the cursor position changes
and sends the proof tree to the browser app defines in `app/`.
- `Examples.lean` - contains example theorems and can be used for testing.
