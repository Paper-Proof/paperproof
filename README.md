# Paper proof Lean widget

![Screen Recording 2023-04-15 at 00 22 03](https://user-images.githubusercontent.com/2538570/232170163-3ef1def1-932d-4f4e-ad0e-ffaaffead01a.gif)

## Overview

WIP: Supposed to be a Lean therorem proving interface (bimodal with VSCode text editing) for iPad and Apple Pencil which feels like you do pen-and-paper proofs.
Currently working on the readonly milestone allowing to visually explore "tactic tree"s of Lean proofs on a spatial canvas (powered by tldraw).

In future potentially with LLMs and visual transformers trying to understand user intent from sketches, formalize to Lean and assist the user. (like in OpenAI GPT 4 demo)

To try the widget

1. Open Example.lean
2. Pin the widget
3. Change cursor to different thereorem or write new proofs
4. See parsed tree in the infoview
5. Run proof server: https://github.com/antonkov/proof-server
6. Open tldraw UI https://github.com/antonkov/tldraw-nodes

## Code structure

- Example.lean contains example theorems and can be used for testing
- Parser.lean contains the parser of InfoTree's into internal TreeState format
- PaperProof.lean defines the widget which constructs a proof tree from the TreeState and sends JSON to the TypeScript code
- widgets/src/paperProof.tsx queries the server method each time cursor changes, displays to infoview and sends to the server which displays in tldraw

## Development

To get started with development, you will need to run these commands first:

```bash
cd widget
yarn install
```

For development run `yarn dev` in command line (it will watch changes in widget ts files and automatically rebuild). Development requires [watchexec](https://watchexec.github.io/), which can be installed by running `cargo install watchexec-cli` if you have Rust toolchain available.

Run `lean4.restartFile` from VSCode when in Lean file to pick up a new widget version.

## TODO

Progress tracker in Notion https://safe-roof-f44.notion.site/Magic-paper-47f3f2c1d3b940428d7d981ea425a601

- [Done] [P0] let definitions should be in the tree too
- [Done] [P1] It would be also nice to print names before the type if we have them
- [Done] [P1] Print as JSON so it can be used from TS
- [Done] Then draw that tree using TLDraw: Attempt 1 ============
- [Done] [P2] We need types of intro'd names like `pln`
- [Done] [P0] !!! I really need to rewrite the code so that it's more readable (see https://github.com/leanprover-community/mathlib4/pull/1218/files)
- [WAI] [P2] ~~refine has ?\_ in the type, we should replace it with the type of the mvar~~ It's actually not a problem, it's a refine syntax which turns ?\_ into goals so it's already displayed. There is a placeholder syntax in Lean with \_ but we don't have to support it yet.

- [P2] Definitions should be recursive too
