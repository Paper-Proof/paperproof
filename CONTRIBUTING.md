# Development

1. **Install the Paperproof vscode extension**

2. **Go to your vscode settings, and change your `Paperproof: Environment` setting to `"Development"`**

    <img width="582" alt="image" src="https://github.com/Paper-Proof/paperproof/assets/7578559/6d56f704-1b65-4ee7-91c0-08396206cc7d">

3. **Install dependencies in /app**

    ```shell
    yarn install
    ```

3. **Start watching your changes in /app**

    ```shell
    yarn server
    ```

    and, in a separate tab:

    ```shell
    yarn watch
    ```

That's it! You can check that everything works by going to `/Examples.lean`, and opening the Paperproof panel by clicking on a piece of a crumpled paper:

  <img width="200" src="https://github.com/Paper-Proof/paperproof/assets/7578559/fd077fbe-36a3-4e94-9fa8-b7a38ffd1eea"/>

You can now change any piece of code within the `/app` folder, and the changes will be built automatically. To see those changes in the webview, you will need to run **Cmd+Shift+P "Developer: Reload Webviews"**.    
If you change some code in `/extension` folder, or in `/lean` folder, seeing the updates is more involved, and that's described in the next section.

# Reload

### Reloading `/app`

If you change something in the `/app` folder, wait for `yarn watch` to compile it, and run **Cmd+Shift+P** `> Developer: Reload Webviews`.

### Reloading `/extension`

If you change something in the `/extension` folder, run

```shell
cd extension
vsce package --out paperproof.vsix
code --uninstall-extension paperproof.paperproof || true
code --install-extension paperproof.vsix
```

and restart vscode (literally - quit it fully, and open it again).

> *ATTENTION: make sure you have yarn v1, otherwise you'll be getting errors from vsce (see [this issue](https://github.com/microsoft/vscode-vsce/issues/517#issuecomment-874323151)).*

> *ATTENTION: if paperproof webview doesn't respond to `.postMessage(...)` calls, AND you have the OUTPUT pane open - close it, and it should start working. It's just some weird vscode glitch.*

### Reloading `/lean`

If you change something in the `/lean` folder, then go to the file where you're checking your code (usually it's `Examples.lean`), and run **Cmd+Shift+P** `> Lean 4: Refresh File Dependencies`.

# Publishing

Deploying our `main` branch consists of 2 steps - publishing a new vscode extension, and publishing a new Paperproof Lean library.

### Deploying `/app` and `/extension`

These folders get published together.  
To deploy them, you need to publish our vscode extension:

1. **Login into vsce**

    ```shell
    vsce login paperproof
    ```

    You will need the *Personal Access Token* for the paperproof organisation to do this (please ask Evgenia or Anton if you need access).

2. **Build and publish**

    ```shell
    vsce publish minor
    ```

    This will autoincrement the `/extension/package.json` version, and publish the Paperproof extension on [marketplace.visualstudio.com/items?itemName=paperproof.paperproof](https://marketplace.visualstudio.com/items?itemName=paperproof.paperproof).  
    Possible increment options are `minor` (nearly always) and `major` (in exceptionally rare cases, only when Paperproof is entirely rewritten).

### Deploying `/lean`

To publish a new Paperproof Lean library, we just push to [github.com/Paper-Proof/paperproof](github.com/Paper-Proof/paperproof) `main` branch.  
The changes will be picked up automatically.

# Code structure

The easiest way to get up to speed with Paperproof's source code is to read [Paperproof Architecture](https://paperproof.brick.do/paperproof-s-architecture-P632P44ezDa9) blog post.  

The 3 folders you'll be working on is:
- `/lean` (parses the Lean proof structure),
- `/app` (contains all the frontend code that you see in the webview), and
- `/extension` (contains VSCode extension code).  

If you want to test the results of your changes, you can go to `Examples.lean`, or to `/_examples/...` for some more test cases.

# Version management

Like mentioned above, Paperproof VSCode extension and Paperproof Lean library are deployed separately; and, correspondingly, users download them separately.  
The **lean library version** and **vscode extension version** should be compatible.  

To ensure such compatibility, we have

- **lean library version**: `.version` field from `/lean/Paperproof.lean`, and
- **vscode extension version**: `desiredVersion` constant in `/app/indexBrowser.lean`

that must *exactly match*.  

If they don't match, we tell the user to update their **lean library version**.  
**Vscode extension version** is always ahead of the game, because VSCode automatically updates the extensions as soon as they are published.

___

There are some other mentions of versioning which have nothing to do with this matching:

- `GlobalContextType.UIVersion` - this is just how we determine when we should rerender the dependency arrows in the ui
- `/extension/package.json version` - this is automatically incremented when we publish vscode extension
- `/app/package.json version`, `/lean/lake-manifest.json version` - NOT USED
- `leanExtension.packageJSON.version` - we check the **vscode-lean4**'s extension version if connecting to their api errors out (this usually means **vscode-lean4** updated their api, and **paperproof** is not yet up to date)

___

Additionally, there is a version of Lean that's used for building the Paperproof library.
There are two Lean versions mentioned in this repo:
- `/lean-toolchain` - this contains a Lean version that's used when you open `code paperproof` In particular, our `/Examples.lean` and `_/examples.lean` always use it.
- `/lean/lean-toolchain` - this contains a Lean version that's used when you open `code paperproof/lean`.

When someone uses Paperproof as a dependency, these versions don't affect anything - the project is built using *their* Lean version.
Our task here is to aim or the largest backwards-compatibility possible.

At the moment we support Lean version in at least [from leanprover/lean4:v4.12.0-rc1, to leanprover/lean4:v4.20.1] range, which is around one year of Lean versions. Our code does raise deprecation warnings for users on v4.20.1 and higher versions of Lean, however we don't upgrade it, as that would break Paperproof for users with Lean v4.12.0. 
We will upgrade it when Paperproof code starts breaking for users on newer versions of Lean.


<div align="center">
<img width="60px" src="https://github.com/Paper-Proof/paperproof/assets/7578559/58f24cf2-4336-4376-8738-6463e3802ba0">
</div>
