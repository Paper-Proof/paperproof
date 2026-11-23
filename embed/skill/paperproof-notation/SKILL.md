---
name: paperproof-notation
description: Write mathematical proofs as Paperproof proof trees (JSON) and embed them in HTML pages with the <paperproof-proof> web component. Use when a web page, textbook or note should show a proof step by step as a tree of goals, hypotheses and steps, or when the user mentions Paperproof or Paperproof notation.
---

# Paperproof notation

A Paperproof tree shows a proof as boxes: each box has a goal, the hypotheses
available in it, and the steps that transform the goal. Arrows show which
hypothesis each new hypothesis or step comes from.

## Workflow

1. Write the proof as JSON in the format described below.
2. Put it into the page:

   ```html
   <script src="https://cdn.jsdelivr.net/npm/paperproof@0.1.2/dist/paperproof-embed.js"></script>

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

   Fix every error. An error means part of the proof is not drawn: a `from` or
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

INTRODUCTION

The user will give you a natural-language proof. Your task is to transform this natural-language proof into the so-called Paperproof Notation (JSON that will be rendered into a tree-like diagram).
Paperproof Notation is heavily inspired by Gentzen Trees, by Lean, and by Formal Logic.
The point of transforming the natural-language proof into the Paperproof Notation is so that the proof structure is apparent - all dependencies are visible, the way the goal is branching out is visible, the ambiguous language is perfectly clarified, and the human can read the proof in Paperproof Notation easily.
Again - we create our JSON for human understanding.

___________

GRANULARITY

There is exactly one correct level of detail: each tactic should correspond to a single atomic step in formal logic - no coarser, no finer. Do not collapse multiple logical steps into one vague sentence, and do not split a single logical step into unnecessary sub-steps.

Exception: you may black-box any theorem or lemma by stating it as the tactic text, prefixed with "Theorem:" (e.g. `"Theorem: every prime > 2 is odd"`). The user will ask you to expand a specific theorem separately if needed.

___________

FORMAL LOGIC RULES

Think of this as Lean - but written for human understanding, not machine verification. Every step should follow one of the standard rules of formal logic:

- ∃-introduction: provide a witness (e.g. "use x")
- ∃-elimination: extract the witness and its property into named hypotheses (e.g. "unfold", "restate")
- ∧-introduction: split into two subgoals (e.g. "split ∧")
- ∧-elimination: extract both conjuncts as named hypotheses (e.g. "unfold", "restate")
- ∨-elimination: case-split on the disjunction
- →-introduction: assume the antecedent, prove the consequent (e.g. "introduce h")
- ∀-introduction: introduce a generic element (e.g. "introduce x")
- ¬-introduction: "assume the opposite" → derive a contradiction → "contradiction"
- Set equality: prove by double inclusion

___________

FORMAT INSTRUCTIONS

type Root = {
  format: "unicode" | "latex";
  goal: string;
  newHyps: Hyp[];
  tactics: Tactic[];
}

type Hyp = {
  name: string;
  type: string;
  from?: string;           // (optional) see below
}

type Tactic = {
  tactic: string;
  newHyps?: Hyp[];         // new hypotheses produced by this step
  newGoal?: string;        // updated goal - use when goal changes but does NOT split
  newSubgoals?: Subgoal[]; // use when this step splits the goal into multiple subgoals
  dependsOn?: string[];    // (optional) see below
  closed?: true;           // this step closes the current goal
}

type Subgoal = {
  goal: string;
  newHyps: Hyp[];
  tactics: Tactic[];
}

Each Tactic must have at least one of: newHyps, newGoal, newSubgoals, closed.

___________

"from" on a hypothesis means: this hypothesis was derived from exactly one parent hypothesis, and after this derivation the parent plays no further role in the proof - the child takes over. Use it whether the derivation is structural (unpacking an existential, destructuring a conjunction) or inferential (e.g. you have `h: p is prime` and in one step conclude `h2: p ≥ 2` by the definition of primality - `h` won't be referenced again, `h2` is what carries the proof forward - use `"from": "h"` on `h2`). The parent is not cited again after this point.

"dependsOn" on a tactic means: this tactic requires these already-established hypotheses as inputs to justify the step. These hypotheses stay in scope - they may be cited again later. Use it when a tactic combines two or more independent facts, or when it invokes a specific named fact without consuming it.

Practical test: if you're deriving a new hypothesis from one parent and the parent is "done," use "from". If a tactic is explicitly invoking one or more named hypotheses that remain relevant after this step, use "dependsOn".

___________

LATEX FORMAT

Use "format": "unicode" by default. Only switch to "format": "latex" if the user explicitly asks for it.

In LaTeX mode, goals and hypothesis types are rendered as full display-mode KaTeX - write them as raw LaTeX with no surrounding $ delimiters:

  "goal": "\\max\\{c^\\top x : Ax \\leq b\\} \\leq \\min\\{y^\\top b : y^\\top A = c^\\top,\\ y \\geq 0\\}"
  "type": "c^\\top x = y^\\top Ax"

Tactic strings are prose with inline math in $...$ delimiters - text outside $ is plain, text inside $ is rendered as KaTeX:

  "tactic": "rewrite $c^\\top x$ as $y^\\top Ax$, using $y^\\top A = c^\\top$"

Because this is JSON, every backslash must be doubled: \leq becomes \\leq, \top becomes \\top, \frac{a}{b} becomes \\frac{a}{b}, etc.

## Examples

### Example 1

Prove: if P ∨ Q, then Q ∨ P.

Proof: Assume h: P ∨ Q. We split into cases on h.
Case 1 (p: P): Q ∨ P holds by taking the right disjunct.
Case 2 (q: Q): Q ∨ P holds by taking the left disjunct.

```json
{
  "format": "unicode",
  "goal": "Q ∨ P",
  "newHyps": [
    {
      "name": "h",
      "type": "P ∨ Q"
    }
  ],
  "tactics": [
    {
      "tactic": "split h",
      "newSubgoals": [
        {
          "goal": "Q ∨ P",
          "newHyps": [
            {
              "name": "p",
              "type": "P",
              "from": "h"
            }
          ],
          "tactics": [
            {
              "tactic": "right",
              "dependsOn": [
                "p"
              ],
              "closed": true
            }
          ]
        },
        {
          "goal": "Q ∨ P",
          "newHyps": [
            {
              "name": "q",
              "type": "Q",
              "from": "h"
            }
          ],
          "tactics": [
            {
              "tactic": "left",
              "dependsOn": [
                "q"
              ],
              "closed": true
            }
          ]
        }
      ]
    }
  ]
}
```

### Example 2

Prove: for sets s and t, s ∩ t = t ∩ s.

Immediate from the definition of intersection and commutativity of conjunction.

```json
{
  "format": "unicode",
  "goal": "s ∩ t = t ∩ s",
  "newHyps": [],
  "tactics": [
    {
      "tactic": "double inclusion",
      "newSubgoals": [
        {
          "goal": "s ∩ t ⊆ t ∩ s",
          "newHyps": [],
          "tactics": [
            {
              "tactic": "introduce x",
              "newHyps": [
                {
                  "name": "h",
                  "type": "x ∈ s ∩ t"
                }
              ],
              "newGoal": "x ∈ t ∩ s"
            },
            {
              "tactic": "definition of ∩",
              "newHyps": [
                {
                  "name": "h",
                  "type": "x ∈ s ∧ x ∈ t",
                  "from": "h"
                }
              ]
            },
            {
              "tactic": "definition of ∩",
              "newGoal": "x ∈ t ∧ x ∈ s"
            },
            {
              "tactic": "commutativity of ∧",
              "dependsOn": [
                "h"
              ],
              "closed": true
            }
          ]
        },
        {
          "goal": "t ∩ s ⊆ s ∩ t",
          "newHyps": [],
          "tactics": [
            {
              "tactic": "introduce x",
              "newHyps": [
                {
                  "name": "h",
                  "type": "x ∈ t ∩ s"
                }
              ],
              "newGoal": "x ∈ s ∩ t"
            },
            {
              "tactic": "definition of ∩",
              "newHyps": [
                {
                  "name": "h",
                  "type": "x ∈ t ∧ x ∈ s",
                  "from": "h"
                }
              ]
            },
            {
              "tactic": "definition of ∩",
              "newGoal": "x ∈ s ∧ x ∈ t"
            },
            {
              "tactic": "commutativity of ∧",
              "dependsOn": [
                "h"
              ],
              "closed": true
            }
          ]
        }
      ]
    }
  ]
}
```
