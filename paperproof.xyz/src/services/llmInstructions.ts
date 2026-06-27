export const exampleJson = `{
  "format": "unicode",
  "goal": "Q ∨ P",
  "newHyps": [
    { "name": "h", "type": "P ∨ Q" }
  ],
  "tactics": [
    {
      "tactic": "cases h",
      "dependsOn": ["h"],
      "newSubgoals": [
        {
          "goal": "Q ∨ P",
          "newHyps": [{ "name": "hp", "type": "P", "from": "h" }],
          "tactics": [
            { "tactic": "exact Or.inr hp", "dependsOn": ["hp"], "closed": true }
          ]
        },
        {
          "goal": "Q ∨ P",
          "newHyps": [{ "name": "hq", "type": "Q", "from": "h" }],
          "tactics": [
            { "tactic": "exact Or.inl hq", "dependsOn": ["hq"], "closed": true }
          ]
        }
      ]
    }
  ]
}`;

export const llmInstructions = `Instructions for writing a Paperproof JSON

A Paperproof JSON turns a natural-language proof into a tree of boxes that mirrors
how the GOAL is broken down until every branch is proved.

CORE PRINCIPLE
1. The proof IS the goal being decomposed. Each step TRANSFORMS the state - it
   introduces a fact, transforms the goal, splits it, or closes it. A step is never
   just a sentence with no effect.
2. Be exactly as detailed as rigor requires - expand every handwave, pad nothing.
   If the source proof leans on a word like "max", "clearly", "symmetric", or "WLOG",
   EXPAND it into the actual argument: leaving it implicit IS handwaving. (E.g.
   "δ = max{cᵀx : x∈P}" must become two facts: cᵀx ≤ δ for all x∈P, AND cᵀx = δ for
   some x∈P.) There is one right level of detail: the smallest fully-rigorous form.

READ THIS EXAMPLE FIRST
Natural-language proof of  s ∩ t = t ∩ s:
  "Take any x. If x ∈ s ∩ t then x ∈ s and x ∈ t, hence x ∈ t and x ∈ s, i.e.
   x ∈ t ∩ s. The reverse direction is symmetric. So the two sets are equal."
As Paperproof JSON - note the goal shrinks each step, the ↔ splits into its two
directions as subgoals, the handwaved "symmetric" direction is written out in full,
rewriting a hyp reuses its name with "from" pointing at itself, and every branch
ends in "closed":
{
  "format": "unicode",
  "goal": "s ∩ t = t ∩ s",
  "newHyps": [
    { "name": "s", "type": "Set ℕ" },
    { "name": "t", "type": "Set ℕ" }
  ],
  "tactics": [
    {
      "tactic": "Introduce x",
      "newHyps": [{ "name": "x", "type": "ℕ" }],
      "newGoal": "x ∈ s ∩ t ↔ x ∈ t ∩ s"
    },
    {
      "tactic": "Split the ↔",
      "newSubgoals": [
        {
          "goal": "x ∈ s ∩ t → x ∈ t ∩ s",
          "newHyps": [],
          "tactics": [
            { "tactic": "Introduce h1", "newHyps": [{ "name": "h1", "type": "x ∈ s ∩ t" }], "newGoal": "x ∈ t ∩ s" },
            { "tactic": "Apply the definition of ∩", "newHyps": [{ "name": "h1", "type": "x ∈ s ∧ x ∈ t", "from": "h1" }] },
            { "tactic": "Commute the ∧", "newHyps": [{ "name": "h1", "type": "x ∈ t ∧ x ∈ s", "from": "h1" }] },
            { "tactic": "Close with h1", "dependsOn": ["h1"], "closed": true }
          ]
        },
        {
          "goal": "x ∈ t ∩ s → x ∈ s ∩ t",
          "newHyps": [],
          "tactics": [
            { "tactic": "Introduce h2", "newHyps": [{ "name": "h2", "type": "x ∈ t ∩ s" }], "newGoal": "x ∈ s ∩ t" },
            { "tactic": "Apply the definition of ∩", "newHyps": [{ "name": "h2", "type": "x ∈ t ∧ x ∈ s", "from": "h2" }] },
            { "tactic": "Commute the ∧", "newHyps": [{ "name": "h2", "type": "x ∈ s ∧ x ∈ t", "from": "h2" }] },
            { "tactic": "Close with h2", "dependsOn": ["h2"], "closed": true }
          ]
        }
      ]
    }
  ]
}

RECIPE
1. Root box: set "format", "goal" = the theorem statement, "newHyps" = the givens.
2. Look at the current goal's shape and break it down:
   - "A → B" or "∀ x, …": one step with "newHyps" (the assumption/variable) + "newGoal" (the body).
   - "∃ x, P":            one step that picks a witness, with "newGoal" P(witness).
   - "A ∧ B" / "A ↔ B":   one step with "newSubgoals", one box per part/direction.
3. Inside a box, each step does one thing: introduce a derived fact ("newHyps"),
   transform the goal ("newGoal"), or finish it ("closed"). Name any fact reused later.
4. Repeat until every leaf box is "closed".

SCHEMA
Box  = { "goal": string, "newHyps": [Hyp], "tactics": [Step] }     // a subgoal / have-box
Root = Box plus { "format": "unicode" | "latex" }                  // only the root has "format"
Hyp  = { "name": string, "type": string, "from"?: string }
Step = { "tactic": string, "dependsOn"?: [string], "newHyps"?: [Hyp],
         "newGoal"?: string, "closed"?: true, "newSubgoals"?: [Box], "haveBoxes"?: [Box] }

- Only list what is NEW in a box/step; ancestor hyps are inherited automatically.
- "name": the hyp's identifier - a short plain label, never LaTeX. Referenced in
  "from"/"dependsOn"; keep the spelling identical everywhere.
- "type" is what the hyp states; "goal" is what remains to prove in this box.
- "from": the hyp this one came from - a rewrite reuses the SAME name + "from" itself;
  a case-split points at the hyp being split. Omit for a fresh fact (variable,
  witness, definition).
- "dependsOn": existing hyps the step consumes. Use sparingly - only load-bearing ones.
- "newSubgoals": a real branch (cases, or the parts of ∧/↔). "haveBoxes": a side-lemma.
- A step MUST carry at least one of newHyps / newGoal / closed / newSubgoals / haveBoxes.

FORMAT
- "unicode": write everything as plain text - "x ∈ s ∩ t", "cases h". No backslashes.
- "latex":
  • "goal"/"type" are pure math: the whole value is bare LaTeX (no $): "c^T x \\le \\delta".
  • a "tactic" is prose with inline math in $...$, like Markdown: "use $\\delta$ as witness".
  • inside math use LaTeX COMMANDS, not unicode: "\\le" not "≤", "x_0" not "x₀", "\\in" not "∈".
  • a "name" is shown verbatim (not via KaTeX), so unicode is fine there ("δ"); it is
    DECOUPLED from the math - a hyp named "δ" is written "\\delta" inside math and
    referenced as "δ" in "from"/"dependsOn".
  • CRITICAL: this is JSON - DOUBLE every backslash ("\\\\le", "\\\\delta"). A single
    backslash fails to parse.

AVOID - the mistakes we actually see
- A FLAT LIST: every step asserting a big conclusion as a "newHyps" while the goal
  never changes until a final "closed". Decompose the goal; prove sub-claims as
  "newSubgoals", not as asserted hyps.
- A PROSE-ONLY step (just "tactic", no delta). Fold narration into a step that acts.
- HANDWAVING: copying "clearly" / "symmetric" / "max" verbatim instead of expanding it.
- "from" on a fresh fact; a "name" that doesn't match its "from"/"dependsOn"; chaining
  distinct claims into one statement ("δ := max{…} < ∞" - split into two).
- (latex) single backslashes; raw unicode inside math.

EXAMPLE - latex mode (every latex rule at once). Proving ∃ x∈ℝ, x ≥ δ for a real δ:
{
  "format": "latex",
  "goal": "\\\\exists x \\\\in \\\\mathbb{R}, \\\\; x \\\\ge \\\\delta",
  "newHyps": [
    { "name": "δ", "type": "\\\\mathbb{R}" }
  ],
  "tactics": [
    {
      "tactic": "use $\\\\delta$ as the witness $x$",
      "dependsOn": ["δ"],
      "newGoal": "\\\\delta \\\\ge \\\\delta"
    },
    {
      "tactic": "true by reflexivity of $\\\\ge$",
      "closed": true
    }
  ]
}`;
