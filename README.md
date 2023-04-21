# Paper proof Lean widget

![Screen Recording 2023-04-15 at 00 22 03](https://user-images.githubusercontent.com/2538570/232170163-3ef1def1-932d-4f4e-ad0e-ffaaffead01a.gif)

## Overview

WIP: Supposed to be a Lean therorem proving interface (bimodal with VSCode text editing) for iPad and Apple Pencil which feels like you do pen-and-paper proofs.
Currently working on the readonly milestone allowing to visually explore "tactic tree"s of Lean proofs on a spatial canvas (powered by tldraw).

In future potentially with LLMs and visual transformers trying to understand user intent from sketches, formalize to Lean and assist the user. (like in OpenAI GPT 4 demo)

## How to use

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
- `widget/src/indexExtension.tsx` - sends the tree to the server and displays the proof tree in the VSCode InfoView.
- `widget/server.cjs` - the Node server that stores and returns our `InfoTree`s; and renders the browser app at `localhost:3000`.

## Development

PaperProof can run both on in the browser (== on ipad) and as a VSCode extension.  
Now, you would usually want to develop the extension in the browser, there is just less clicking this way.

### Develop while looking at the browser [prefferred]

First, do `cd widget` and run `yarn install`. Then:

- `yarn run watchBrowser` - this compiles both the browser app and the reduced version of the vscode extension (this reduced version just sends `InfoTree`s to our node server as you hover over the lines in a proof).
- `node server.cjs` - this starts the node server that 1. memorizes the `InfoTree` information that the browser app then queries 2. renders the browser app at http://localhost:3000..
- `node server.cjs` - this starts the node server that:
  1. memorizes the `InfoTree` information which widget sends and the browser app later queries
  2. renders the browser app at http://localhost:3000.

### Develop while looking at the VSCode extension

First, do `cd widget` and run `yarn install`. Then:

- `yarn run watchExtension` - this compiles the VSCode extension.

That's it. But don't be deceived - every time you update your tldraw code, you will need to execute `lean4.restartFile` from VSCode in the `PaperProof.lean`; and click around a few times. Also - vscode seems to cache stuff? In general - it's a slower development cycle.

## Links

Progress tracker in Notion https://safe-roof-f44.notion.site/Magic-paper-47f3f2c1d3b940428d7d981ea425a601