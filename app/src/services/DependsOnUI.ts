import { GlobalContextType } from "src/indexBrowser";
import getHypById from "./getHypById";
import { HypNode } from "types";
import FancySubstring from "./FancySubstring";

const shouldDrawArrowToHypothesis = (global: GlobalContextType, hypId: string): boolean => {
  if (global.settings.isSingleTacticMode) {
    return false;
  } else {
    const hyp = getHypById(global.proofTree, hypId);
    return !!hyp && hyp.isProof === "proof";
  }
}

const shouldHighlightHypothesis = (global: GlobalContextType, hypNode: HypNode): boolean => {
  if (global.settings.isSingleTacticMode) {
    const singleTactic = global.proofTree.tactics[1];
    return singleTactic &&
      singleTactic.dependsOnIds.includes(hypNode.id) &&
      (
        hypNode.isProof === "proof" ||
        (!!hypNode.name && FancySubstring.findAllMatches(singleTactic.text, hypNode.name).length > 0)
      );
  } else {
    return !!global.highlights && global.highlights.hypIds.includes(hypNode.id);
  }
}

export default {
  shouldDrawArrowToHypothesis,
  shouldHighlightHypothesis
};
