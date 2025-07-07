import React from 'react';
import { GlobalContextType } from 'src/indexBrowser';
import FancySubstring from './FancySubstring';

const fancySubstringHypotheses = (text: string, global: GlobalContextType): React.ReactNode => {
  if (!global.settings.isSingleTacticMode) return text
  if (!global.settings.areHypsHighlighted) return text

  // Collect all "data" hypotheses from the proof tree
  const proofHypothesisNames = global.proofTree.boxes
    .flatMap(box => box.hypLayers)
    .flatMap(layer => layer.hypNodes)
    .filter(hypNode => hypNode.isProof === "data")
    .map(hypNode => hypNode.name)
    .filter(name => name !== null);

  return FancySubstring.renderTextWithMatches(text, [
    {
      items: proofHypothesisNames,
      getItemString: (hypName) => hypName,
      renderMatch: (match, index, text) => (
        <span key={`hypothesis-${index}`} className="fancy-substring-hypothesis">
          {text.substring(match.start, match.end)}
        </span>
      )
    }
  ]);
};

export default fancySubstringHypotheses;
