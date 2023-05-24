# Paper proof

<div align="left">
  <a href="https://www.youtube.com/watch?v=FKni19OCqH0&ab_channel=AntonKovsharov">
      <img src="https://img.youtube.com/vi/FKni19OCqH0/0.jpg">
  </a>
</div>

https://www.tldraw.com/v/mlp_c_7vS7iofiWJ6_fwACbZyr?viewport=-2196%2C-8449%2C5257%2C2744&page=page%3Ai9kaf9cVmFmT3-gbYZmJD

## Overview

WIP: Supposed to be a Lean therorem proving interface (bimodal with VSCode text editing) for iPad and Apple Pencil which feels like you do pen-and-paper proofs.
Currently working on the readonly milestone allowing to visually explore "tactic tree"s of Lean proofs on a spatial canvas (powered by tldraw).

In future potentially with LLMs and visual transformers trying to understand user intent from sketches, formalize to Lean and assist the user. (like in OpenAI GPT 4 demo)

## Developement

1. Install the extension from `extension/` folder
```console
code --install-extension extension/tactictree-0.0.1.vsix
```

2. Run the dev server (you might need to run `yarn install` first)
```console
cd app; yarn dev
```

3. Toggle the view with "Tactic Tree: Toggle" command (Ctrl+Shift+P) or open in browser on
http://localhost:3000

## Reload 

As you iterate on code reload the browser page
or "Toggle Tactic Tree" to hide and show again.

## Code structure

- `lean/` - defines the custom Lean server method which parses the InfoTree into appropriate format for visualization.
- `app/` - contains a simple server and the browser app which renders
the proof tree.
- `extension/` - contains the VSCode extension which queries the Lean server method defined in `lean/` each time the cursor position changes
and sends the proof tree to the browser app defines in `app/`.
- `Examples.lean` - contains example theorems and can be used for testing.

## Links

Progress tracker in Notion https://safe-roof-f44.notion.site/Magic-paper-47f3f2c1d3b940428d7d981ea425a601
