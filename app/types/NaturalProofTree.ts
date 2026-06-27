// ─────────────────────────────────────────────────────────────────────────────
// NaturalProofTree — the hand-written / LLM-authored proof format.
//
// A proof is a tree of boxes. Each box carries only its OWN delta:
//   - goal:    the goal at the top of this box
//   - newHyps: hypotheses introduced on entry (ancestors' hyps are inherited)
//   - tactics: the steps taken inside this box
// A hypothesis optionally names where it came from via `from` (drives the arrow).
//
// `nestedToConverted` turns this into a ConvertedProofTree for rendering;
// `copyAsNestedBoxes` produces this from a real Lean proof.
// ─────────────────────────────────────────────────────────────────────────────

export interface NaturalHyp {
  name: string;
  type: string;
  from?: string; // name of the hyp this one descends from; omitted = appears from nothing
}

export interface NaturalStep {
  tactic: string;
  dependsOn?: string[];        // hyp names this step consumes (arrows hyp → tactic node)
  newHyps?: NaturalHyp[];      // hyps this step introduces
  newGoal?: string;            // if the goal transforms within this box
  closed?: true;               // this step closes the current goal
  newSubgoals?: NaturalBox[];  // case split: each subgoal is its own box
  haveBoxes?: NaturalBox[];    // side-proofs of a lemma (`have`)
}

export interface NaturalBox {
  goal: string;
  newHyps: NaturalHyp[];
  tactics: NaturalStep[];
}

// The top-level proof. `format` is REQUIRED here (and only here): the author/LLM
// must commit to one notation for the whole proof — plain unicode, or LaTeX
// (rendered via KaTeX). Nested subgoals/have-boxes are plain `NaturalBox`es.
export interface NaturalProofTree extends NaturalBox {
  format: "unicode" | "latex";
}
