# Development

1. Install the extension, fully close and open vscode.

   ```shell
   cd extension
   code --uninstall-extension paperproof.paperproof || true
   code --install-extension paperproof.vsix
   ```

2. Go to your vscode settings, and change your `Paperproof: Environment` setting to `"Development"`.

<img width="582" alt="image" src="https://github.com/Paper-Proof/paperproof/assets/7578559/6d56f704-1b65-4ee7-91c0-08396206cc7d">

3. Start watching your changes.

   ```shell
   cd app
   yarn server
   yarn watch
   ```

That's it! You can check that everything works by going to `/Examples.lean`, and opening the Paperproof panel by clicking on a piece of a crumpled paper:

  <img width="200" src="https://github.com/Paper-Proof/paperproof/assets/7578559/fd077fbe-36a3-4e94-9fa8-b7a38ffd1eea"/>

You can now change any piece of code within the `/app` folder, and the changes will be built automatically. To see those changes in the webview, you will need to run **Cmd+Shift+P "Developer: Reload Webviews"**.  
If you change something it `/extension`, or in `/lean`, seeing the updates is more involved, and that's described in the next section.

# Reload

## Reloading `/app`

If you change something in the `/app` folder, wait for `yarn watch` to compile it, and run **Cmd+Shift+P** `> Developer: Reload Webviews`.

## Reloading `/extension`

If you change something in the `/extension` folder, run

```shell
cd extension
vsce package --out paperproof.vsix
code --uninstall-extension paperproof.paperproof || true
code --install-extension paperproof.vsix
```

and restart vscode (literally - quit it fully, and open it again).

## Reloading `/lean`

If you change something in the `/lean` folder, then go to the file where you're checking your code, usually it's `Examples.lean`, and run **Cmd+Shift+P** `> Lean 4: Refresh File Dependencies`.

# Publishing

Deploying our `main` branch consists of 2 steps - publishing a new vscode extension, and publishing a new Paperproof Lean library.

## Deploying `/extension`

To deploy a vscode Paperproof extension:

1. Login into vsce

```shell
vsce login paperproof
```

You will need the Personal Access Token for the paperproof organisation to do this (please ask Evgenia or Anton if you need access).

2. Build and publish

```shell
vsce publish patch
```

This will autoincrement the `/extension/package.json` version, and publish the extension on https://marketplace.visualstudio.com/items?itemName=paperproof.paperproof.
Possible increment options are `major`, `minor`, and `patch`.

## Deploying `/lean`

To publish a new Paperproof Lean library, we just push to [github.com/Paper-Proof/paperproof](github.com/Paper-Proof/paperproof) `main` branch, the changes will be picked up automatically.

# Code structure

- `lean/` - defines the custom Lean server method which parses the InfoTree into appropriate format for visualization.
- `app/` - contains a simple server and the browser app which renders
  the proof tree.
- `extension/` - contains the VSCode extension which queries the Lean server method defined in `lean/` each time the cursor position changes
  and sends the proof tree to the browser app defines in `app/`.
- `Examples.lean` - contains example theorems and can be used for testing.
