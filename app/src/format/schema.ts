import * as z from "zod/mini";
import { en } from "zod/locales";
import type { NaturalBox, NaturalHyp, NaturalProofTree, NaturalStep } from "types";

z.config(en());

const Hyp: z.ZodMiniType<NaturalHyp> = z.object({
  name: z.string(),
  type: z.string(),
  from: z.optional(z.string()),
});

const Step: z.ZodMiniType<NaturalStep> = z.object({
  tactic: z.string(),
  dependsOn: z.optional(z.array(z.string())),
  newHyps: z.optional(z.array(Hyp)),
  newGoal: z.optional(z.string()),
  closed: z.optional(z.literal(true)),
  get newSubgoals() { return z.optional(z.array(Box)); },
  get haveBoxes() { return z.optional(z.array(Box)); },
});

const Box: z.ZodMiniType<NaturalBox> = z.object({
  goal: z.string(),
  newHyps: z.array(Hyp),
  get tactics() { return z.array(Step); },
});

export const NaturalProofTreeSchema: z.ZodMiniType<NaturalProofTree> = z.object({
  format: z.enum(["unicode", "latex"]),
  goal: z.string(),
  newHyps: z.array(Hyp),
  tactics: z.array(Step),
});

const keysOf = (schema: z.ZodMiniType) => Object.keys((schema as unknown as z.ZodMiniObject)._zod.def.shape);

export const KEYS = {
  proof: keysOf(NaturalProofTreeSchema),
  box: keysOf(Box),
  hyp: keysOf(Hyp),
  step: keysOf(Step),
};

export const naturalProofTreeJsonSchema = () => z.toJSONSchema(NaturalProofTreeSchema, { target: "draft-7" });
