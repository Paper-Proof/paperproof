# Paper proof Lean widget

https://www.tldraw.com/v/mlp_c_7vS7iofiWJ6_fwACbZyr?viewport=-2196%2C-8449%2C5257%2C2744&page=page%3Ai9kaf9cVmFmT3-gbYZmJD

## Overview

WIP: Supposed to be a Lean therorem proving interface (bimodal with VSCode text editing) for iPad and Apple Pencil which feels like you do pen-and-paper proofs.
Currently working on the readonly milestone allowing to visually explore "tactic tree"s of Lean proofs on a spatial canvas (powered by tldraw).

In future potentially with LLMs and visual transformers trying to understand user intent from sketches, formalize to Lean and assist the user. (like in OpenAI GPT 4 demo)

## How to use as VSCode Extension 

1. Install the extension from extension folder

`code --install-extension tactictree-0.0.1.vsix`

2. Run the server

`node widget/server.cjs`

2. Open `Example.lean`

3. Toggle the view with "Toggle Tactic Tree" command (Ctrl+Shift+P) or open in browser on
http://localhost:3000

## How to use as Lean Infoview widget [old]

https://youtu.be/n7-vmiRPtyQ

1. Build the developer version of the widget (see the development section below).
Later simplified production version will be supported.
2. Open `Example.lean`
3. Put cursor over a widget line and pin the widget in Infoview
4. Change cursor between theorems to see different proofs at http://localhost:3000

## Code structure

- `Example.lean` - contains example theorems and can be used for testing
- `Parser.lean` - contains the parser of InfoTree's into internal TreeState format
- `PaperProof.lean` - defines the widget which constructs a proof tree from the TreeState and sends JSON to the TypeScript code
- `widget/src/indexBrowser.tsx` - displays the proof tree in the browser at `localhost:3000`.
- `widget/src/indexInfoview.tsx` - TODO: supposed to query Lean server and display the tree in the Lean
Infoview,
- `widget/server.cjs` - the Node server that stores and returns our `InfoTree`s; and renders the browser app at `localhost:3000`.

## Development

PaperProof runs in the browser (== on ipad).
It's considered to be running as a Lean Infoview widget as well but not fully supported yet.

### Develop while looking at the browser [prefferred]

First, do `cd widget` and run `yarn install`. Then:

- `yarn run watchBrowser` - this compiles both the browser app and the reduced version of the vscode extension (this reduced version just sends `InfoTree`s to our node server as you hover over the lines in a proof).
- `node server.cjs` - this starts the node server that:
  1. memorizes the `InfoTree` information which widget sends and the browser app later queries
  2. renders the browser app at http://localhost:3000.

### Develop while looking at the Lean Infoview

NOTE: That's not recommended for developement and currently doesn't display anything.
Lean Infoview allows only a single JS file for the widget but tldraw requires css and assets.
Since now we use tldraw for rendering - Lean Infoview doesn't display anything.

First, do `cd widget` and run `yarn install`. Then:

- `yarn run watchInfoview` - this compiles the VSCode extension.

That's it. But don't be deceived - every time you update your tldraw code, you will need to execute `lean4.restartFile` from VSCode in the `PaperProof.lean`; and click around a few times. Also - vscode seems to cache stuff? In general - it's a slower development cycle.

## Links

Progress tracker in Notion https://safe-roof-f44.notion.site/Magic-paper-47f3f2c1d3b940428d7d981ea425a601
