import { SNAPSHOT_VERSION, SnapshotPayload, SnapshotState } from "types";

const paperproofXYZ = 'https://paperproof.xyz'

export const createSnapshot = async (state: SnapshotState): Promise<string> => {
  const payload: SnapshotPayload = { version: SNAPSHOT_VERSION, ...state };

  const response = await fetch(`${paperproofXYZ}/api/snapshot`, {
    method: 'POST',
    headers: {
      'Content-Type': 'application/json',
    },
    body: JSON.stringify(payload),
  });

  if (!response.ok) {
    throw new Error(`Failed to create snapshot: ${response.statusText}`);
  }

  const result = await response.json();
  return `${paperproofXYZ}/${result.id}`;
};
