const hyp = {
  type: "object",
  required: ["name", "type"],
  additionalProperties: false,
  properties: {
    name: { type: "string" },
    type: { type: "string" },
    from: { type: "string" },
  },
};

const step = {
  type: "object",
  required: ["tactic"],
  additionalProperties: false,
  anyOf: [
    { required: ["newHyps"] },
    { required: ["newGoal"] },
    { required: ["closed"] },
    { required: ["newSubgoals"] },
    { required: ["haveBoxes"] },
  ],
  properties: {
    tactic: { type: "string" },
    dependsOn: { type: "array", items: { type: "string" } },
    newHyps: { type: "array", minItems: 1, items: { $ref: "#/$defs/hyp" } },
    newGoal: { type: "string" },
    closed: { type: "boolean" },
    newSubgoals: { type: "array", minItems: 1, items: { $ref: "#/$defs/box" } },
    haveBoxes: { type: "array", minItems: 1, items: { $ref: "#/$defs/box" } },
  },
};

const box = {
  type: "object",
  required: ["goal", "tactics"],
  additionalProperties: false,
  properties: {
    goal: { type: "string" },
    newHyps: { type: "array", items: { $ref: "#/$defs/hyp" } },
    tactics: { type: "array", items: { $ref: "#/$defs/step" } },
  },
};

const rootBox = {
  type: "object",
  required: ["goal", "tactics", "format"],
  additionalProperties: false,
  properties: {
    goal: { type: "string" },
    format: { type: "string", enum: ["unicode", "latex"] },
    newHyps: { type: "array", items: { $ref: "#/$defs/hyp" } },
    tactics: { type: "array", items: { $ref: "#/$defs/step" } },
  },
};

export const proofSchema = {
  $ref: "#/$defs/rootBox",
  $defs: { hyp, step, box, rootBox },
};
