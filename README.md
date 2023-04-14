# Paper proof Lean widget

## Overview

To try the widget

1. Open Example.lean
2. Pin the widget
3. Change cursor to different thereorem or write new proofs
4. See parsed tree in the infoview

Optionally 5. Run proof server 6. Open tldraw UI

## Code structure

- Example.lean contains example theorems and can be used for testing
- Parser.lean contains the parser of InfoTree's into internal TreeState format
- PaperProof.lean is the file defines the widget which constructs a proof tree from the TreeState sends JSON to the TypeScript code
- widgets/src/paperProof.tsx quires the server method each time cursor changes, displays to infoview and sends to the server which displays in tldraw

## Development

To get started with development, you will need to run these commands first:

```bash
cd widget
yarn install
```

For development run `yarn dev` in command line (it will watch changes in widget ts files and automatically rebuild). Development requires [watchexec](https://watchexec.github.io/), which can be installed by running `cargo install watchexec-cli` if you have Rust toolchain available.

Run `lean4.restartFile` from VSCode when in Lean file to pick up a new widget version.

## TODO

- [Done] [P0] let definitions should be in the tree too
- [Done] [P1] It would be also nice to print names before the type if we have them
- [Done] [P1] Print as JSON so it can be used from TS
- ==== Then draw that tree using TLDraw: Attempt 1 ============
- [Done] [P2] We need types of intro'd names like `pln`
- [P0] !!! I really need to rewrite the code so that it's more readable (see https://github.com/leanprover-community/mathlib4/pull/1218/files)
- [P3] Definitions should be recursive too
- ==== Then draw that tree using TLDraw: Attempt 2 ============
- [P2] refine has ?\_ in the type, we should replace it with the type of the mvar
