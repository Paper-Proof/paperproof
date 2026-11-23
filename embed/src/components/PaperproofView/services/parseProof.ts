import { ConvertedProofTree, DEFAULT_LATEX_SETTINGS, Highlights, LatexSettings, LeanProofTree, Settings, SNAPSHOT_VERSION, SnapshotPayload } from "types";
import converter from "@app/services/converter";
import hypsToTables from "@app/services/hypsToTables";
import naturalToConverted from "@app/services/naturalToConverted";
import { collectTexts } from "@app/services/convertToLatex";
import { validate, Problem } from "@app/format";

export interface View {
  tree: ConvertedProofTree;
  settings: Settings;
  highlights: Highlights;
  collapsedBoxIds: string[];
  deletedHypothesisNames: string[];
  latexSettings: LatexSettings;
}

export type Parsed =
  | { kind: "lean" | "snapshot" | "natural"; view: View; problems: Problem[] }
  | { kind: "invalid"; problems: Problem[] }
  | { kind: "error"; message: string };

const withHypTables = (tree: ConvertedProofTree, settings: Settings): ConvertedProofTree => ({
  ...tree,
  boxes: tree.boxes.map((box) => ({ ...box, hypTables: hypsToTables(box.hypLayers, tree, settings.isSingleTacticMode) })),
});

const latexSettingsOf = (tree: ConvertedProofTree): LatexSettings => {
  const { stable, changing } = collectTexts(tree);
  const map: Record<string, string> = {};
  for (const text of [...stable, ...changing]) map[text] = text;
  return { ...DEFAULT_LATEX_SETTINGS, isActive: true, map };
};

const leanSteps = (proof: unknown): LeanProofTree | null => {
  if (Array.isArray(proof)) return proof;
  const steps = (proof as { steps?: unknown } | null)?.steps;
  return Array.isArray(steps) ? steps : null;
};

const parseLean = (steps: LeanProofTree, settings: Settings): Parsed => {
  if (steps.length === 0) return { kind: "error", message: "this proof has no steps" };
  const tree = withHypTables(converter(steps), settings);
  return {
    kind: "lean",
    view: { tree, settings, highlights: null, collapsedBoxIds: [], deletedHypothesisNames: [], latexSettings: DEFAULT_LATEX_SETTINGS },
    problems: [],
  };
};

const parseSnapshot = (snapshot: SnapshotPayload): Parsed => {
  if (!snapshot.proofTree.boxes) return { kind: "error", message: "this snapshot has no proof in it" };
  if (snapshot.version > SNAPSHOT_VERSION) return { kind: "error", message: "this snapshot was made by a newer version of Paperproof" };
  const { settings, highlights, collapsedBoxIds, deletedHypothesisNames, latexSettings } = snapshot;
  return {
    kind: "snapshot",
    view: { tree: withHypTables(snapshot.proofTree, settings), settings, highlights, collapsedBoxIds, deletedHypothesisNames, latexSettings },
    problems: [],
  };
};

const parseNatural = (proof: unknown, settings: Settings): Parsed => {
  const { tree: natural, problems } = validate(proof);
  if (!natural) return { kind: "invalid", problems };
  const tree = withHypTables(naturalToConverted(natural), settings);
  const latexSettings = natural.format === "latex" ? latexSettingsOf(tree) : DEFAULT_LATEX_SETTINGS;
  return {
    kind: "natural",
    view: { tree, settings, highlights: null, collapsedBoxIds: [], deletedHypothesisNames: [], latexSettings },
    problems,
  };
};

export const parseProof = (proof: unknown, settings: Settings): Parsed => {
  try {
    const steps = leanSteps(proof);
    if (steps) return parseLean(steps, settings);
    if ((proof as SnapshotPayload | null)?.proofTree) return parseSnapshot(proof as SnapshotPayload);
    return parseNatural(proof, settings);
  } catch (e) {
    return { kind: "error", message: e instanceof Error ? e.message : String(e) };
  }
};
