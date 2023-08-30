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

### Code structure

- `lean/` - defines the custom Lean server method which parses the InfoTree into appropriate format for visualization.
- `app/` - contains a simple server and the browser app which renders
the proof tree.
- `extension/` - contains the VSCode extension which queries the Lean server method defined in `lean/` each time the cursor position changes
and sends the proof tree to the browser app defines in `app/`.
- `Examples.lean` - contains example theorems and can be used for testing.
