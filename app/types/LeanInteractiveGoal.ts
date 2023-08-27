export interface LeanInteractiveHyp {
  // `fvarIds` and `names` are always of the same length
  fvarIds: string[];
  names: string[];
  // type with all the stuff that lets us hover over it
  type: object;
}

export interface LeanInteractiveGoal {
  ctx: object;
  goalPrefix: string;
  hyps: LeanInteractiveHyp[];
  mvarId: string;
  // type with all the stuff that lets us hover over it
  type: object;
  userName: string;
}
