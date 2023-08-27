import { ConvertedProofTree } from "types";

// Copypaste from converter.js (changed the argument names though, for no serious reason, needs to be made the same)
const getDisplayedId = (equivalentIds: ConvertedProofTree["equivalentIds"], id: string) => {
  const displayedId = Object.keys(equivalentIds).find((displayedId) =>
    equivalentIds[displayedId].find((inferiorId) => inferiorId === id)
  );
  return displayedId ? displayedId : id;
};

export default getDisplayedId;
