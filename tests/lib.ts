import naturalToConverted from "@app/services/naturalToConverted";
import { collectTexts } from "@app/services/convertToLatex";
import { DEFAULT_LATEX_SETTINGS, LatexSettings, NaturalProofTree, Settings, SNAPSHOT_VERSION, SnapshotPayload } from "types";

export const snapshotPayload = (proof: NaturalProofTree, settings: Partial<Settings> = {}): SnapshotPayload => {
  const proofTree = naturalToConverted(proof);
  let latexSettings: LatexSettings = DEFAULT_LATEX_SETTINGS;
  if (proof.format === "latex") {
    const { stable, changing } = collectTexts(proofTree);
    const map: Record<string, string> = {};
    for (const text of [...stable, ...changing]) map[text] = text;
    latexSettings = { ...DEFAULT_LATEX_SETTINGS, isActive: true, map };
  }
  return {
    version: SNAPSHOT_VERSION,
    proofTree,
    settings: {
      isSingleTacticMode: false,
      isHiddenGoalNames: false,
      isGreenHypotheses: false,
      areHypsHighlighted: false,
      isFollowingCursor: false,
      isUnlimitedWidth: false,
      fontSize: 12,
      ...settings,
    },
    highlights: null,
    collapsedBoxIds: [],
    deletedHypothesisNames: [],
    latexSettings,
  };
};

export { validate, formatProblems } from "@app/format";
