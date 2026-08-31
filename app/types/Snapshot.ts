import { ConvertedProofTree, Highlights, LatexSettings, Settings } from "types";

/**
 * [Claude comment]
 * Bump whenever a change would make the current renderer misread an older
 * payload, and migrate the old version in `snapshotRenderer.tsx`.
 *
 * - 1: `{ proofTreeHTML }`, a frozen outerHTML dump. Snapshots taken then are
 *      still served as-is from their `.html` file, so nothing needs migrating.
 * - 2: this.
 */
export const SNAPSHOT_VERSION = 2;

export interface SnapshotPayload {
  version: number;
  proofTree: ConvertedProofTree;
  settings: Settings;
  highlights: Highlights;
  collapsedBoxIds: string[];
  deletedHypothesisNames: string[];
  latexSettings: LatexSettings;
}

export type SnapshotState = Omit<SnapshotPayload, "version">;
