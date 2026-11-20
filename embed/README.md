# @paperproof/embed

Render Paperproof proof trees in any web page, from JSON that a person or an LLM
writes. The format is `NaturalProofTree`, the one `/playground` uses.

```html
<script src="https://cdn.jsdelivr.net/npm/@paperproof/embed@0.1.0/dist/paperproof-embed.js"></script>

<paperproof-proof>
  <script type="application/json">
    {"format": "unicode", "goal": "Q ∨ P", "newHyps": [{"name": "h", "type": "P ∨ Q"}], "tactics": [ … ]}
  </script>
</paperproof-proof>
```

| attribute | |
|---|---|
| `fit="scroll"` | keep a wide tree at full size, with its own horizontal scrollbar; by default it is scaled down to the column, on screen and in print |
| `fit="none"` | keep a wide tree at full size and let it run past the column, so the page scrolls |
| `font-size="13"` | text size in px (default 12) |
| `unlimited-width` | don't cap nodes at 200px, so no text wraps |
| `theme="sand"` | how a step that closes a goal looks: `sand` (default), `cyan` (the extension's), `check`, `square`, `check-goal`, `slate`, `clay` |
| `dark-bars` | darker HYPOTHESES and THEOREM bars, with any theme |
| `src="proof.json"` | load the JSON from a file instead of the inline `<script>` (needs http) |
| `kind="snapshot"` | the JSON is a snapshot payload from the VS Code extension rather than a `NaturalProofTree` |

Right-click a tree to pick a theme or switch the dark bars on or off. The browser keeps the
choice for every tree on the site, and it overrides `theme` and `dark-bars`.

`element.proof = json` replaces the proof. Each tree renders in its own shadow root,
so the page's CSS doesn't reach it and its CSS doesn't reach the page.

Pages that must work offline (or from `file://`) can copy `dist/paperproof-embed.js`
next to them. LaTeX-format proofs load KaTeX from jsDelivr.

Problems in a proof (an unknown `from`/`dependsOn` name, a step that changes nothing)
are listed in red under the tree; `window.Paperproof.validate(json)` returns the same list.

## CLI

```bash
npx @paperproof/embed validate page.html proofs/*.json   # exit code 1 on errors
npx @paperproof/embed render page.html --index 0 --out proof.png
npx @paperproof/embed schema         # JSON Schema of the format
npx @paperproof/embed instructions   # how to write proofs, for LLMs
```

`validate` reads `.json` files as one proof each and finds every `<paperproof-proof>`
block in any other file. `render` needs Chrome (`CHROME_PATH` if it isn't found).

## For LLMs

`skill/paperproof-notation/SKILL.md` is an Agent Skill: the format, the embed snippet
and the write → validate → render loop. `dist/llms.txt` is the same text. Both are
generated from `app/src/format/llmInstructions.js`.

## Build

```bash
npm install
node build.mjs     # → dist/paperproof-embed.js, dist/cli.cjs, dist/schema.json, dist/llms.txt, skill/
```

The renderer and the format come from `app/` (React from `app/node_modules`); the
published package has no dependencies. `examples/demo.html` shows a unicode proof, a
LaTeX proof, a broken proof, a wide one, and every theme.
