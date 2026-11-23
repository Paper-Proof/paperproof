export const llmInstructions = `INTRODUCTION

The user will give you a natural-language proof. Your task is to transform this natural-language proof into the so-called Paperproof Notation (JSON that will be rendered into a tree-like diagram).
Paperproof Notation is heavily inspired by Gentzen Trees, by Lean, and by Formal Logic.
The point of transforming the natural-language proof into the Paperproof Notation is so that the proof structure is apparent - all dependencies are visible, the way the goal is branching out is visible, the ambiguous language is perfectly clarified, and the human can read the proof in Paperproof Notation easily.
Again - we create our JSON for human understanding.

___________

GRANULARITY

There is exactly one correct level of detail: each tactic should correspond to a single atomic step in formal logic - no coarser, no finer. Do not collapse multiple logical steps into one vague sentence, and do not split a single logical step into unnecessary sub-steps.

Exception: you may black-box any theorem or lemma by stating it as the tactic text, prefixed with "Theorem:" (e.g. \`"Theorem: every prime > 2 is odd"\`). The user will ask you to expand a specific theorem separately if needed.

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
}

type Tactic = {
  tactic: string;
  newHyps?: Hyp[];         // new hypotheses produced by this step
  newGoal?: string;        // updated goal - use when goal changes but does NOT split
  newSubgoals?: Subgoal[]; // use when this step splits the goal into multiple subgoals
  dependsOn?: string[];    // hypotheses this step uses
  closed?: true;           // this step closes the current goal
}

type Subgoal = {
  goal: string;
  newHyps: Hyp[];
  tactics: Tactic[];
}

Each Tactic must have at least one of: newHyps, newGoal, newSubgoals, closed.

___________

LATEX FORMAT

Use "format": "unicode" by default. Only switch to "format": "latex" if the user explicitly asks for it.

In LaTeX mode, goals and hypothesis types are rendered as full display-mode KaTeX - write them as raw LaTeX with no surrounding $ delimiters:

  "goal": "\\\\max\\\\{c^\\\\top x : Ax \\\\leq b\\\\} \\\\leq \\\\min\\\\{y^\\\\top b : y^\\\\top A = c^\\\\top,\\\\ y \\\\geq 0\\\\}"
  "type": "c^\\\\top x = y^\\\\top Ax"

Tactic strings are prose with inline math in $...$ delimiters - text outside $ is plain, text inside $ is rendered as KaTeX:

  "tactic": "rewrite $c^\\\\top x$ as $y^\\\\top Ax$, using $y^\\\\top A = c^\\\\top$"

Because this is JSON, every backslash must be doubled: \\leq becomes \\\\leq, \\top becomes \\\\top, \\frac{a}{b} becomes \\\\frac{a}{b}, etc.`;

export const fewShotExamples = [
  {
    text: `Prove: if P ∨ Q, then Q ∨ P.

Proof: Assume h: P ∨ Q. We split into cases on h.
Case 1 (p: P): Q ∨ P holds by taking the right disjunct.
Case 2 (q: Q): Q ∨ P holds by taking the left disjunct.`,
    json: `{"format":"unicode","goal":"Q ∨ P","newHyps":[{"name":"h","type":"P ∨ Q"}],"tactics":[{"tactic":"split h","dependsOn":["h"],"newSubgoals":[{"goal":"Q ∨ P","newHyps":[{"name":"p","type":"P"}],"tactics":[{"tactic":"right","dependsOn":["p"],"closed":true}]},{"goal":"Q ∨ P","newHyps":[{"name":"q","type":"Q"}],"tactics":[{"tactic":"left","dependsOn":["q"],"closed":true}]}]}]}`,
  },
  {
    text: `Prove: for sets s and t, s ∩ t = t ∩ s.

Immediate from the definition of intersection and commutativity of conjunction.`,
    json: `{"format":"unicode","goal":"s ∩ t = t ∩ s","newHyps":[],"tactics":[{"tactic":"double inclusion","newSubgoals":[{"goal":"s ∩ t ⊆ t ∩ s","newHyps":[],"tactics":[{"tactic":"introduce x","newHyps":[{"name":"h","type":"x ∈ s ∩ t"}],"newGoal":"x ∈ t ∩ s"},{"tactic":"definition of ∩","dependsOn":["h"],"newHyps":[{"name":"h","type":"x ∈ s ∧ x ∈ t"}]},{"tactic":"definition of ∩","newGoal":"x ∈ t ∧ x ∈ s"},{"tactic":"commutativity of ∧","dependsOn":["h"],"closed":true}]},{"goal":"t ∩ s ⊆ s ∩ t","newHyps":[],"tactics":[{"tactic":"introduce x","newHyps":[{"name":"h","type":"x ∈ t ∩ s"}],"newGoal":"x ∈ s ∩ t"},{"tactic":"definition of ∩","dependsOn":["h"],"newHyps":[{"name":"h","type":"x ∈ t ∧ x ∈ s"}]},{"tactic":"definition of ∩","newGoal":"x ∈ s ∧ x ∈ t"},{"tactic":"commutativity of ∧","dependsOn":["h"],"closed":true}]}]}]}`,
  },
  {
    text: `Theorem 4.7.4 Infinitude of the Primes

The set of prime numbers is infinite.

Proof (by contradiction):

Suppose not. That is, suppose the set of prime numbers is finite. [We must deduce a contradiction.] Then some prime number p is the largest of all the prime numbers, and hence we can list the prime numbers in ascending order:

2, 3, 5, 7, 11, …, p.

Let N be the product of all the prime numbers plus 1:

N = (2·3·5·7·11···p) + 1

Then N > 1, and so, by Theorem 4.3.4, N is divisible by some prime number q. Because q is prime, q must equal one of the prime numbers 2, 3, 5, 7, 11, …, p.

Thus, by definition of divisibility, q divides 2·3·5·7·11···p, and so, by Proposition 4.7.3, q does not divide (2·3·5·7·11···p) + 1, which equals N. Hence N is divisible by q and N is not divisible by q, and we have reached a contradiction. [Therefore, the supposition is false and the theorem is true.] ∎`,
    json: `{"format":"unicode","goal":"set of prime numbers is infinite","newHyps":[],"tactics":[{"tactic":"assume the opposite","newGoal":"contradiction","newHyps":[{"name":"h_finite","type":"set of prime numbers is finite"}]},{"tactic":"multiply all prime numbers, add 1","dependsOn":["h_finite"],"newHyps":[{"name":"N","type":"2 * 3 * 5 * ... * p + 1"}]},{"tactic":"because N is bigger than all prime numbers, it must be composite","dependsOn":["N"],"newHyps":[{"name":"one","type":"N > 1"},{"name":"N_is_composite","type":"N is composite"}]},{"tactic":"Theorem 4.3.4","dependsOn":["one","N_is_composite"],"newHyps":[{"name":"q_exists","type":"∃ q, (q is prime) ∧ (q | N)"}]},{"tactic":"unfold","dependsOn":["q_exists"],"newHyps":[{"name":"q","type":"ℕ"},{"name":"q_is_prime","type":"q is prime"},{"name":"q_divides_N","type":"q | N"}]},{"tactic":"q is prime, and we multiplied all prime numbers","dependsOn":["q_is_prime"],"newHyps":[{"name":"q_is_one_of_primes","type":"q is one of 2, 3, 5, 7, ..., p"}]},{"tactic":"if q is one of [a,b,c], then q can divide a*b*c ","dependsOn":["q_is_one_of_primes"],"newHyps":[{"name":"q_divides","type":"q | 2 * 3 * 5 * 7 * ... * p"}]},{"tactic":"Proposition 4.7.3","dependsOn":["q_divides"],"newHyps":[{"name":"q_doesnt_divide_N","type":"q ∤ (2 * 3 * 5 * 7 * ... * p) + 1"}]},{"tactic":"definition of N","dependsOn":["q_doesnt_divide_N"],"newHyps":[{"name":"q_doesnt_divide_N","type":"q ∤ N"}]},{"tactic":"contradiction","dependsOn":["q_doesnt_divide_N","q_divides_N"],"closed":true}]}`,
  },
  {
    text: `Proposition 2.7. Let P = P(A,b) ≠ ∅ be a polyhedron and F ⊆ P. The following statements are equivalent.
(a) F is a face of P, i.e., F = P or F is the intersection of P with a supporting hyperplane of P.
(b) There is a vector c s.t. δ := max{cᵀx : x ∈ P} < ∞ and F = {x ∈ P : cᵀx = δ}.
(c) There is a sub-system A′x ≤ b′ of Ax ≤ b such that F = {x ∈ P : A′x = b′} ≠ ∅.
Proof.
To conclude (b) from (c), define cᵀ as the sum of row vectors in A′ and δ as the sum of entries in b′. Now, cᵀx ≤ δ ∀x ∈ P and F = {x ∈ P : cᵀx = δ}.`,
    json: `{"format":"unicode","goal":"(b) There is a vector c s.t. δ := max{cᵀx : x ∈ P} < ∞ and F = {x ∈ P : cᵀx = δ}.","newHyps":[{"name":"F_in_P","type":"F ⊆ P"},{"name":"c","type":"(c) There is a sub-system A′x ≤ b′ of Ax ≤ b such that F = {x ∈ P : A′x = b′} ≠ ∅."}],"tactics":[{"tactic":"restate","newGoal":"∃ c, δ, max{cᵀx : x ∈ P} = δ ∧ F = {x ∈ P : cᵀx = δ}"},{"tactic":"restate","dependsOn":["c"],"newHyps":[{"name":"c","type":"∃ (A′, b′), A′x ≤ b′ is a subsystem of Ax ≤ b ∧ F = {x ∈ P : A′x = b′} ∧ F ≠ ∅"}]},{"tactic":"restate","dependsOn":["c"],"newHyps":[{"name":"A'b'","type":"A′x ≤ b′ is a subsystem of Ax ≤ b"},{"name":"F_definition","type":"F = {x ∈ P : A′x = b′}"},{"name":"F_not_empty","type":"F ≠ ∅"}]},{"tactic":"use c := Σ rows of A′, use δ := Σ entries of b′","newGoal":"max{cᵀx : x ∈ P} = δ ∧ F = {x ∈ P : cᵀx = δ}","newHyps":[{"name":"sum_of_A'b'_inequalities","type":"c := Σ rows of A′; δ := Σ entries of b′"}]},{"tactic":"split ∧","newSubgoals":[{"goal":"max{cᵀx : x ∈ P} = δ","newHyps":[],"tactics":[{"tactic":"unfold max","newSubgoals":[{"goal":"∀ x ∈ P, cᵀx ≤ δ","newHyps":[],"tactics":[{"tactic":"if a₁ ≤ b₁; a₂ ≤ b₂ then a₁ + a₂ ≤ b₁ + b₂","dependsOn":["A'b'"],"closed":true}]},{"goal":"∃ y ∈ P, cᵀy = δ","newHyps":[],"tactics":[{"tactic":"F is not empty","dependsOn":["F_not_empty","F_definition"],"newHyps":[{"name":"h","type":"∃ y ∈ P, A′y = b′"}]},{"tactic":"restate","dependsOn":["h"],"newHyps":[{"name":"y","type":"y ∈ P"},{"name":"h","type":"A′y = b′"}]},{"tactic":"use y","newGoal":"cᵀy = δ"},{"tactic":"if a₁ = b₁; a₂ = b₂ then a₁ + a₂ = b₁ + b₂","dependsOn":["h"],"closed":true}]}]}]},{"goal":"F = {x ∈ P : cᵀx = δ}","newHyps":[],"tactics":[{"tactic":"double inclusion","newSubgoals":[{"goal":"F ⊆ {x ∈ P : cᵀx = δ}","newHyps":[],"tactics":[{"tactic":"introduce x","newHyps":[{"name":"h","type":"x ∈ F"}],"newGoal":"x ∈ {x ∈ P : cᵀx = δ}"},{"tactic":"simplify","newGoal":"cᵀx = δ"},{"tactic":"F_definition","dependsOn":["h"],"newHyps":[{"name":"h","type":"A′x = b′"}]},{"tactic":"if a₁ = b₁; a₂ = b₂ then a₁ + a₂ = b₁ + b₂","dependsOn":["h"],"closed":true}]},{"goal":"{x ∈ P : cᵀx = δ} ⊆ F","newHyps":[],"tactics":[{"tactic":"introduce x","newHyps":[{"name":"h","type":"x ∈ {x ∈ P : cᵀx = δ}"}],"newGoal":"x ∈ F"},{"tactic":"F_definition","newGoal":"A′x = b′"},{"tactic":"simplify","dependsOn":["h"],"newHyps":[{"name":"h","type":"cᵀx = δ"}]},{"tactic":"if a₁ ≤ b₁; a₂ ≤ b₂; a₁ + a₂ = b₁ + b₂ then a₁ = b₁; a₂ = b₂","dependsOn":["h","A'b'"],"closed":true}]}]}]}]}]}`
  }
];
