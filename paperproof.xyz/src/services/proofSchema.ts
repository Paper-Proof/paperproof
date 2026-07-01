import { z } from "zod";
import { zodToJsonSchema } from "zod-to-json-schema";

const NaturalHypSchema = z.object({
  name: z.string(),
  type: z.string(),
  from: z.string().optional(),
});

// NaturalBox and NaturalStep are mutually recursive — z.lazy() breaks the cycle.
type NaturalBox = {
  goal: string;
  newHyps: z.infer<typeof NaturalHypSchema>[];
  tactics: NaturalStep[];
};

type NaturalStep = {
  tactic: string;
  dependsOn?: string[];
  newHyps?: z.infer<typeof NaturalHypSchema>[];
  newGoal?: string;
  closed?: true;
  newSubgoals?: NaturalBox[];
  haveBoxes?: NaturalBox[];
};

const NaturalBoxSchema: z.ZodType<NaturalBox> = z.lazy(() =>
  z.object({
    goal: z.string(),
    newHyps: z.array(NaturalHypSchema),
    tactics: z.array(NaturalStepSchema),
  })
);

const NaturalStepSchema: z.ZodType<NaturalStep> = z.lazy(() =>
  z.object({
    tactic: z.string(),
    dependsOn: z.array(z.string()).optional(),
    newHyps: z.array(NaturalHypSchema).optional(),
    newGoal: z.string().optional(),
    closed: z.literal(true).optional(),
    newSubgoals: z.array(NaturalBoxSchema).optional(),
    haveBoxes: z.array(NaturalBoxSchema).optional(),
  })
);

export const NaturalProofTreeSchema = z.object({
  format: z.enum(["unicode", "latex"]),
  goal: z.string(),
  newHyps: z.array(NaturalHypSchema),
  tactics: z.array(NaturalStepSchema),
});

export const proofJsonSchema = zodToJsonSchema(NaturalProofTreeSchema, { name: "NaturalProofTree" });
