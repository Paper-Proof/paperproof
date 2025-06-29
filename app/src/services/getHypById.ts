import { ConvertedProofTree, HypNode } from "types";

const getHypById = (convertedProofTree: ConvertedProofTree, hypId: string | null): HypNode | null => {
  if (hypId === null) return null
  for (const box of convertedProofTree.boxes) {
    const foundHyp = box.hypLayers
      .flatMap(layer => layer.hypNodes)
      .find(hypNode => hypNode.id === hypId);
    
    if (foundHyp) {
      return foundHyp;
    }
  }

  return null;
}

export default getHypById;
