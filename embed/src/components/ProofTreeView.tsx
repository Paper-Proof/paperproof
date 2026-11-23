import React from "react";
import { ConvertedProofTree, Highlights, LatexSettings, Position, Settings, fakePosition } from "types";

import BoxEl from "@app/components/ProofTree/components/BoxEl";
import areWeOnEllipsisTactic from "@app/services/areWeOnEllipsisTactic";

import { GlobalContext, useGlobalContext } from "@app/globalContext";

export const DEFAULT_SETTINGS: Settings = {
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
  setSettings?: (x: Settings) => void;
  collapsedBoxIds: string[];
  setCollapsedBoxIds: (x: string[]) => void;
  deletedHypothesisNames: string[];
  setDeletedHypothesisNames: (x: string[]) => void;
  latexSettings: LatexSettings;
  setLatexSettings?: (x: LatexSettings) => void;
  position?: Position;
}

const RootBox = () => {
  const { proofTree } = useGlobalContext();
  const rootBox = proofTree.boxes.find((box) => box.parentId === null);
  if (!rootBox) return null;
  return <BoxEl box={rootBox}/>;
};

const ProofTreeView = (props: Props) => {
  const [UIVersion, setUIVersion] = React.useState<number>(1);
  const proofTreeRef = React.useRef<HTMLDivElement>(null);

  const refreshUI = React.useCallback(() => setUIVersion((version) => version + 1), []);

  // [Claude comment] Arrows are measured off the DOM, so they're wrong until the
  // webfonts land and the text reflows.
  React.useEffect(() => {
    const tree = proofTreeRef.current;
    if (!tree) return;
    let size = "";
    const observer = new ResizeObserver(() => {
      const now = `${tree.offsetWidth}x${tree.offsetHeight}`;
      if (now !== size) { size = now; refreshUI(); }
    });
    observer.observe(tree);
    return () => observer.disconnect();
  }, [refreshUI]);

  React.useEffect(() => {
    let isStale = false;
    document.fonts.ready.then(() => { if (!isStale) refreshUI(); });
    return () => { isStale = true; };
  }, [refreshUI]);

  return (
    <GlobalContext.Provider
      value={{
        UIVersion, refreshUI,
        collapsedBoxIds: props.collapsedBoxIds, setCollapsedBoxIds: props.setCollapsedBoxIds,
        deletedHypothesisNames: props.deletedHypothesisNames, setDeletedHypothesisNames: props.setDeletedHypothesisNames,
        settings: props.settings,               setSettings: props.setSettings ?? (() => {}),

        proofTree: props.proofTree,
        highlights: props.highlights,
        position: props.position ?? fakePosition,
        setConverted: () => {},
        createSnapshot: async () => "",
        setSnackbarMessage: () => {},
        setSnackbarOpen: () => {},
        proofTreeRef,
        fetchFullProofTree: async () => props.proofTree,
        latexSettings: props.latexSettings, setLatexSettings: props.setLatexSettings ?? (() => {}),
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
        ref={proofTreeRef}
        style={{ '--box-font-size': `${props.settings.fontSize}px` } as React.CSSProperties}
      >
        <RootBox/>
      </div>
    </GlobalContext.Provider>
  );
};

export default ProofTreeView;
