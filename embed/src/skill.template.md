---
name: paperproof-notation
description: Write mathematical proofs as Paperproof proof trees (JSON) and embed them in HTML pages with the <paperproof-proof> web component. Use when a web page, textbook or note should show a proof step by step as a tree of goals, hypotheses and steps, or when the user mentions Paperproof or Paperproof notation.
---

# Paperproof notation

A Paperproof tree shows a proof as boxes: each box has a goal, the hypotheses
available in it, and the steps that transform the goal. Arrows show which
hypotheses each step uses.

## Workflow

1. Write the proof as JSON in the format described below.
2. Put it into the page:

   ```html
   <script src="https://cdn.jsdelivr.net/npm/paperproof@{{VERSION}}/dist/paperproof-embed.js"></script>

   <paperproof-proof>
     <script type="application/json">
       {"format": "unicode", "goal": "…", "newHyps": [], "tactics": […]}
     </script>
   </paperproof-proof>
   ```

   - Load the script once per page; it can go in `<head>`.
   - A tree wider than the column is scaled down to fit. `fit="scroll"` keeps it
     at full size with its own scrollbar, and `fit="none"` lets it run past the
     column so the page scrolls. `font-size="13"` changes the text size
     (default 12).
   - Goals, steps and hypotheses are at most 200px wide and wrap longer text; the
     root box spans the column. `unlimited-width` removes the cap, which suits
     proofs with long formulas inside branches.
   - `theme="..."` sets how a step that closes a goal looks: `sand` (default),
     `cyan` (the VS Code extension's), `check`, `square`. `dark-bars` makes the
     HYPOTHESES and THEOREM bars darker, with any theme.
   - `src="proof.json"` loads the JSON from a file instead (needs http, not file://).
   - For pages that must work offline, copy `dist/paperproof-embed.js` next to
     the page and load it with a relative path. LaTeX-format proofs load KaTeX
     from jsDelivr.

3. Check every proof on the page:

   ```bash
   npx paperproof validate page.html
   ```

   Fix every error. An error means part of the proof is not drawn: a
   `dependsOn` name that is not in scope gets no arrow, and a step without any
   effect is invalid. Warnings mean the tree probably does not show what you
   meant: an unclosed goal, steps after a goal was closed, or several goal
   effects on one step (only the first is drawn). The page also lists errors in
   red under the tree.

4. Look at the result:

   ```bash
   npx paperproof render page.html --index 0 --out proof.png
   ```

   and view the PNG (needs Chrome; set `CHROME_PATH` if it is not found).

`npx paperproof schema` prints the JSON Schema of the format.

## The format

{{INSTRUCTIONS}}

## Examples

{{EXAMPLES}}
