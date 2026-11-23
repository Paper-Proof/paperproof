export interface NaturalHyp {
  name: string;
  type: string;
}

export interface NaturalStep {
  tactic: string;
  dependsOn?: string[];
  newHyps?: NaturalHyp[];
  newGoal?: string;
  closed?: true;
  newSubgoals?: NaturalBox[];
  haveBoxes?: NaturalBox[];
}

export interface NaturalBox {
  goal: string;
  newHyps: NaturalHyp[];
  tactics: NaturalStep[];
}

export interface NaturalProofTree extends NaturalBox {
  format: "unicode" | "latex";
}
