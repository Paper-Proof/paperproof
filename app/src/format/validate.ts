import type { NaturalBox, NaturalHyp, NaturalProofTree, NaturalStep } from "types";
import { KEYS, NaturalProofTreeSchema } from "./schema";

export interface Problem {
  level: "error" | "warning";
  path: string;
  message: string;
}

export interface ValidationResult {
  ok: boolean;
  problems: Problem[];
  tree?: NaturalProofTree;
}

const pathToString = (path: ReadonlyArray<PropertyKey>): string =>
  path.reduce<string>((acc, key) =>
    typeof key === "number" ? `${acc}[${key}]` : acc ? `${acc}.${String(key)}` : String(key), "") || "(root)";

const inScope = (scope: Set<string>): string => {
  const names = [...scope];
  if (names.length === 0) return "no hypotheses are in scope here";
  const shown = names.slice(-12).map((n) => `"${n}"`).join(", ");
  return `in scope here: ${shown}${names.length > 12 ? ", …" : ""}`;
};

const unknownKeys = (tree: any): Problem[] => {
  const problems: Problem[] = [];
  const check = (obj: any, path: string, allowed: string[]) => {
    for (const key of Object.keys(obj)) {
      if (!allowed.includes(key)) {
        problems.push({ level: "warning", path: path ? `${path}.${key}` : key, message: `unknown key "${key}" is ignored (allowed: ${allowed.join(", ")})` });
      }
    }
  };
  const box = (b: any, path: string, allowed: string[]) => {
    check(b, path, allowed);
    b.newHyps.forEach((h: any, i: number) => check(h, `${path ? `${path}.` : ""}newHyps[${i}]`, KEYS.hyp));
    b.tactics.forEach((s: any, i: number) => {
      const p = `${path ? `${path}.` : ""}tactics[${i}]`;
      check(s, p, KEYS.step);
      (s.newHyps ?? []).forEach((h: any, j: number) => check(h, `${p}.newHyps[${j}]`, KEYS.hyp));
      (s.newSubgoals ?? []).forEach((sub: any, j: number) => box(sub, `${p}.newSubgoals[${j}]`, KEYS.box));
      (s.haveBoxes ?? []).forEach((have: any, j: number) => box(have, `${p}.haveBoxes[${j}]`, KEYS.box));
    });
  };
  box(tree, "", KEYS.proof);
  return problems;
};

export const validate = (input: unknown): ValidationResult => {
  const parsed = NaturalProofTreeSchema.safeParse(input);
  if (!parsed.success) {
    return {
      ok: false,
      problems: parsed.error.issues.map((issue) => ({ level: "error" as const, path: pathToString(issue.path), message: issue.message })),
    };
  }
  const tree = parsed.data;
  const problems: Problem[] = unknownKeys(input);
  const error = (path: string, message: string) => problems.push({ level: "error", path, message });
  const warning = (path: string, message: string) => problems.push({ level: "warning", path, message });

  const addLayer = (hyps: NaturalHyp[], path: string, scope: Set<string>) => {
    const seen = new Set<string>();
    hyps.forEach((hyp, i) => {
      const hypPath = `${path}[${i}]`;
      if (seen.has(hyp.name)) {
        warning(`${hypPath}.name`, `"${hyp.name}" is introduced twice in the same step; later references will point at this second one`);
      }
      seen.add(hyp.name);
      scope.add(hyp.name);
    });
  };

  const checkLatex = (text: string, path: string) => {
    const dollars = (text.match(/(?<!\\)\$/g) ?? []).length;
    if (dollars % 2 === 1) warning(path, `odd number of "$" in a LaTeX-format tactic, so part of it renders as math by mistake`);
  };

  const walkBox = (box: NaturalBox, path: string, parentScope: Set<string>): boolean => {
    const scope = new Set(parentScope);
    addLayer(box.newHyps, path ? `${path}.newHyps` : "newHyps", scope);

    let closed = false;
    box.tactics.forEach((step: NaturalStep, i) => {
      const stepPath = `${path ? `${path}.` : ""}tactics[${i}]`;
      const label = `step "${step.tactic}"`;

      if (closed) warning(stepPath, `${label} comes after the goal of this box was closed; it is drawn but proves nothing`);
      if (tree.format === "latex") checkLatex(step.tactic, `${stepPath}.tactic`);

      (step.dependsOn ?? []).forEach((name, j) => {
        if (!scope.has(name)) {
          error(`${stepPath}.dependsOn[${j}]`, `${label} depends on "${name}", which is not a hypothesis in scope, so no arrow is drawn (${inScope(scope)})`);
        }
      });

      const goalEffects = ([
        ["closed", !!step.closed],
        ["haveBoxes", !!step.haveBoxes?.length],
        ["newSubgoals", !!step.newSubgoals?.length],
        ["newGoal", step.newGoal !== undefined],
      ] as const).filter(([, present]) => present).map(([key]) => key);
      const hasHyps = !!step.newHyps?.length;

      if (goalEffects.length === 0 && !hasHyps) {
        error(stepPath, `${label} changes nothing: give it at least one of newHyps, newGoal, newSubgoals, closed`);
      }
      if (goalEffects.length > 1) {
        warning(stepPath, `${label} sets ${goalEffects.join(" and ")}; only "${goalEffects[0]}" is drawn, the rest is ignored`);
      }
      if (step.newSubgoals?.length === 1) {
        warning(`${stepPath}.newSubgoals`, `${label} has a single subgoal; use newGoal unless the step really branches`);
      }

      if (hasHyps) addLayer(step.newHyps!, `${stepPath}.newHyps`, scope);

      if (step.closed) {
        closed = true;
      } else if (step.haveBoxes?.length) {
        step.haveBoxes.forEach((have, j) => {
          const havePath = `${stepPath}.haveBoxes[${j}]`;
          if (!walkBox(have, havePath, scope)) warning(havePath, `the side-proof of "${have.goal}" is never closed`);
        });
      } else if (step.newSubgoals?.length) {
        step.newSubgoals.forEach((sub, j) => {
          const subPath = `${stepPath}.newSubgoals[${j}]`;
          if (!walkBox(sub, subPath, scope)) warning(subPath, `the subgoal "${sub.goal}" is never closed: end it with a step that has "closed": true`);
        });
        closed = true;
      }
    });
    return closed;
  };

  if (!walkBox(tree, "", new Set())) {
    warning("(root)", `the goal "${tree.goal}" is never closed: end the proof with a step that has "closed": true, or split it with newSubgoals`);
  }

  return { ok: !problems.some((p) => p.level === "error"), problems, tree };
};

export const formatProblems = (problems: Problem[]): string =>
  problems.map((p) => `${p.level === "error" ? "error  " : "warning"} ${p.path}: ${p.message}`).join("\n");
