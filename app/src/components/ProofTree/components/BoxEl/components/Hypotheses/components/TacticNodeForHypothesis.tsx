import React from "react";
import { TabledTactic } from "types";
import BoxEl from "src/components/ProofTree/components/BoxEl";
import TacticNode from "src/components/TacticNode";
import { useGlobalContext } from "src/indexBrowser";
import flashElement from "src/services/flashElement";

interface Props {
  cell: TabledTactic;
  colSpan: number;
}
const TacticNodeForHypothesis = (props: Props) => {
  const tactic = props.cell.tactic;
  // TODO Evgenia: this is where we stopped - we likely want to move all of this to <TacticNode/>
  const global = useGlobalContext();
  const { collapsedBoxIds, setCollapsedBoxIds, refreshUI } = global;

  if (tactic.text === "init") return null

  const hasChildrenBoxes = tactic.haveBoxIds.length > 0
  const isBoxHidden = tactic.haveBoxIds.find((id1) => collapsedBoxIds.find((id2) => id1 === id2))

  // Collapsing/expanding moves everything below this tactic, so flash it
  const flashThisTactic = () => {
    const el = document.getElementById(
      props.cell.shardId ? `tactic-${tactic.id}-${props.cell.shardId}` : `tactic-${tactic.id}`
    );
    if (el) flashElement(el);
  }

  const hideAllChildrenBoxes = (event: React.MouseEvent) => {
    event.preventDefault();
    event.stopPropagation();

    const selection = window.getSelection();
    const isUserIsCopypasting = selection && selection.toString().length > 0;
    if (isUserIsCopypasting) return

    setCollapsedBoxIds([...collapsedBoxIds, ...tactic.haveBoxIds])
    flashThisTactic();
    refreshUI();
  }
  const showAllChildrenBoxes = (event: React.MouseEvent) => {
    event.preventDefault();
    event.stopPropagation();

    const selection = window.getSelection();
    const isUserIsCopypasting = selection && selection.toString().length > 0;
    if (isUserIsCopypasting) return

    setCollapsedBoxIds(collapsedBoxIds.filter((b) => !tactic.haveBoxIds.includes(b)))
    flashThisTactic();
    refreshUI();
  }

  const onClick = (event: React.MouseEvent) => {
    if (global.settings.isSingleTacticMode) return
    if (!hasChildrenBoxes) return
    if (isBoxHidden) {
      showAllChildrenBoxes(event)
    } else {
      hideAllChildrenBoxes(event)
    }
  }

  return (
    <>
      {
        tactic.haveBoxIds.length > 0 &&
        <div className="child-boxes">
          {tactic.haveBoxIds.map((haveBoxId) => (
            !isBoxHidden &&
            <BoxEl
              key={haveBoxId}
              box={global.proofTree.boxes.find((box) => box.id === haveBoxId)!}
            />
          ))}
        </div>
      }
      <TacticNode
        className="-hypothesis-tactic"
        tactic={props.cell.tactic}
        shardId={props.cell.shardId}
        onClick={onClick}
        circleEl={
          hasChildrenBoxes &&
          (isBoxHidden ?
          <button type="button" className="show-boxes">
            {/* An SVG rather than "⛶" (U+26F6) - that glyph comes from a fallback
                symbol font with no bold cut, so `font-weight` couldn't thicken it.
                Same four-corners shape, but the weight is `stroke-width`. */}
            <svg viewBox="0 0 24 24" aria-hidden="true"><path d="M8 3H3v5M16 3h5v5M16 21h5v-5M8 21H3v-5"/></svg>
          </button> :
          <button type="button" className="hide-boxes">▬</button>)
        }
      />
    </>
  );
};

export default TacticNodeForHypothesis;
