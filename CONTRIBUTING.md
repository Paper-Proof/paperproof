## Development

1. Install the extension from `/extension` folder

    ```console
    cd extension; code --install-extension paperproof.vsix
    ```

2. Run the dev server

    ```shell
    cd app
    yarn install
    yarn dev
    ```

3. Go to your vscode settings, and change your `Paperproof: Server Url` setting to `http://localhost:80`. Close & reopen vscode.

<img width="467" alt="image" src="https://github.com/Paper-Proof/paperproof/assets/7578559/13539e57-2a66-4067-9193-b5e324984d2f">
<img width="478" alt="image" src="https://github.com/Paper-Proof/paperproof/assets/7578559/fb775762-4e3f-468b-94ef-5abbd1cd2593">

4. Go to `/Examples.lean`, and open the Paperpoof panel by running **Cmd+Shift+P** `> Paperproof: Toggle`, or just by clicking on a piece of a crumpled paper:

    <img width="200" src="https://github.com/Paper-Proof/paperproof/assets/7578559/fd077fbe-36a3-4e94-9fa8-b7a38ffd1eea"/>

### Reload 

#### Reloading /app

If you change something in the `/app` folder, wait for yarn to compile it, and run **Cmd+Shift+P** `> Developer: Reload Webviews`.

#### Reloading /extension

If you change something in the `/extension` folder, run

```shell
vsce package --out paperproof.vsix; code --uninstall-extension paperproof.paperproof; code --install-extension paperproof.vsix
```
and restart VSCode (literally - quit it fully, and restart it).

#### Reloading /lean

If you change something in the `/lean` folder, then go to the file where you're checking your code, usually it's `Examples.lean`, and run **Cmd+Shift+P** `> Lean 4: Refresh File Dependencies`.


### Publishing

Deploying our `main` branch consists of 3 steps - deploying to paperproof.xyz, publishing a new vscode extension, and publishing a new Paperproof Lean library.

#### Deploying /app

To deploy [paperproof.xyz](paperproof.xyz) contents:

1. Go to https://github.com/Paper-Proof/paperproof/actions/workflows/deploy-do.yml
2. Run the "Deploy to Digital Ocean" workflow

#### Deploying /extension

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

#### Deploying /lean

To publish a new Paperproof Lean library, we just push to [github.com/Paper-Proof/paperproof](github.com/Paper-Proof/paperproof) `main` branch, the changes will be picked up automatically.

### Code structure

- `lean/` - defines the custom Lean server method which parses the InfoTree into appropriate format for visualization.
- `app/` - contains a simple server and the browser app which renders
the proof tree.
- `extension/` - contains the VSCode extension which queries the Lean server method defined in `lean/` each time the cursor position changes
and sends the proof tree to the browser app defines in `app/`.
- `Examples.lean` - contains example theorems and can be used for testing.
