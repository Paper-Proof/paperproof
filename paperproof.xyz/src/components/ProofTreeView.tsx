import React from "react";
import { Arrow, ConvertedProofTree, Highlights, LatexSettings, Settings, fakePosition } from "types";

import BoxEl from "@app/components/ProofTree/components/BoxEl";
import PerfectArrow from "@app/components/PerfectArrow";
import createHypArrows from "@app/services/createHypArrows";
import areWeOnEllipsisTactic from "@app/services/areWeOnEllipsisTactic";

import { StandaloneGlobalContext, useStandaloneGlobalContext } from "../proofContext";

export const DEFAULT_STANDALONE_SETTINGS: Settings = {
  isSingleTacticMode: false,
  isHiddenGoalNames : false,
  isGreenHypotheses : false,
  areHypsHighlighted: false,
  isFollowingCursor : false,
  isUnlimitedWidth  : false,
  fontSize          : 12,
};

interface Props {
  proofTree: ConvertedProofTree;
  highlights: Highlights;
  settings: Settings;
  setSettings: (x: Settings) => void;
  collapsedBoxIds: string[];
  setCollapsedBoxIds: (x: string[]) => void;
  deletedHypothesisNames: string[];
  setDeletedHypothesisNames: (x: string[]) => void;
  latexSettings: LatexSettings;
  setLatexSettings: (x: LatexSettings) => void;
}

const RootBox = () => {
  const { proofTree } = useStandaloneGlobalContext();
  const rootBox = proofTree.boxes.find((box) => box.parentId === null);
  if (!rootBox) return null;
  return <BoxEl box={rootBox}/>;
};

// [Claude comment] The tree outside of vscode - /playground and snapshot pages.
// Fully controlled; all it adds is the arrow layer.
const ProofTreeView = (props: Props) => {
  const [UIVersion, setUIVersion] = React.useState<number>(1);
  const [searchedHypIds, setSearchedHypIds] = React.useState<string[]>([]);
  const [perfectArrows, setPerfectArrows] = React.useState<Arrow[]>([]);

  const refreshUI = React.useCallback(() => setUIVersion((version) => version + 1), []);

  React.useLayoutEffect(() => {
    setPerfectArrows(createHypArrows(props.proofTree));
  }, [props.proofTree, props.latexSettings, UIVersion]);

  // [Claude comment] Arrows are measured off the DOM, so they're wrong until the
  // webfonts land and the text reflows.
  React.useEffect(() => {
    let isStale = false;
    document.fonts.ready.then(() => { if (!isStale) refreshUI(); });
    return () => { isStale = true; };
  }, [refreshUI]);

  return (
    <StandaloneGlobalContext.Provider
      value={{
        UIVersion, refreshUI,
        collapsedBoxIds: props.collapsedBoxIds, setCollapsedBoxIds: props.setCollapsedBoxIds,
        searchedHypIds,                         setSearchedHypIds,
        deletedHypothesisNames: props.deletedHypothesisNames, setDeletedHypothesisNames: props.setDeletedHypothesisNames,
        settings: props.settings,               setSettings: props.setSettings,

        proofTree: props.proofTree,
        highlights: props.highlights,
        // [Claude comment] Nothing out here has a cursor, so no tactic ever counts as the current one
        position: fakePosition,
        setConverted: () => {},
        createSnapshot: async () => "",
        setSnackbarMessage: () => {},
        setSnackbarOpen: () => {},
        isStandalone: true,
        fetchFullProofTree: async () => props.proofTree,
        latexSettings: props.latexSettings, setLatexSettings: props.setLatexSettings,
      }}
    >
      <div
        className={`
          proof-tree
          ${props.settings.isSingleTacticMode ? '-isSingleTacticModeON' : ''}
          ${props.settings.isHiddenGoalNames ? '-isHiddenGoalNamesON' : ''}
          ${props.settings.isUnlimitedWidth ? '-isUnlimitedWidthON' : ''}
          ${props.settings.isGreenHypotheses ? ''                     : '-isGreenHypothesesOFF'}
          ${areWeOnEllipsisTactic(props.proofTree, props.highlights) ? '-we-are-on-ellipsis-tactic' : ''}
          ${props.latexSettings.isActive ? '-isLatexModeON' : ''}
        `}
        style={{ '--box-font-size': `${props.settings.fontSize}px` } as React.CSSProperties}
      >
        <RootBox/>
        {perfectArrows.map((arrow, index) =>
          <PerfectArrow key={index} p1={arrow.from} p2={arrow.to}/>
        )}
      </div>
    </StandaloneGlobalContext.Provider>
  );
};

export default ProofTreeView;
