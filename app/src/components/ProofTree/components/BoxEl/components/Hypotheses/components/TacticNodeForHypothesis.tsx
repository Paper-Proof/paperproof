import React, { useState } from "react";
import { TabledTactic } from "types";
import BoxEl from "src/components/ProofTree/components/BoxEl";
import TacticNode from "src/components/TacticNode";
import { useGlobalContext } from "src/indexBrowser";

interface Props {
  cell: TabledTactic;
  colSpan: number;
  shouldTacticHaveSelfRespect: boolean
}
const TacticNodeForHypothesis = (props: Props) => {
  const tactic = props.cell.tactic;
  const global = useGlobalContext();

  if (tactic.text === "init") return null

  // TODO Evgenia: this is where we stopped - we likely want to move all of this to <TacticNode/>
  const { collapsedBoxIds, setCollapsedBoxIds, refreshUI } = useGlobalContext();

  const hasChildrenBoxes = tactic.haveBoxIds.length > 0
  const isBoxHidden = tactic.haveBoxIds.find((id1) => collapsedBoxIds.find((id2) => id1 === id2))

  const hideAllChildrenBoxes = (event: React.MouseEvent) => {
    event.preventDefault();
    event.stopPropagation();

    const selection = window.getSelection();
    const isUserIsCopypasting = selection && selection.toString().length > 0;
    if (isUserIsCopypasting) return

    setCollapsedBoxIds([...collapsedBoxIds, ...tactic.haveBoxIds])
    setBackgroundColor(true);
    setTimeout(() => {
      setBackgroundColor(false);
    }, 500);
    refreshUI();
  }
  const showAllChildrenBoxes = (event: React.MouseEvent) => {
    event.preventDefault();
    event.stopPropagation();

    const selection = window.getSelection();
    const isUserIsCopypasting = selection && selection.toString().length > 0;
    if (isUserIsCopypasting) return

    setCollapsedBoxIds(collapsedBoxIds.filter((b) => !tactic.haveBoxIds.includes(b)))
    setBackgroundColor(true);
    setTimeout(() => {
      setBackgroundColor(false);
    }, 500);
    refreshUI();
  }

  const [backgroundColor, setBackgroundColor] = useState<boolean>(false);

  const onClick = (event: React.MouseEvent) => {
    if (global.settings.isSingleTacticMode) return
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
        className={`
          -hypothesis-tactic
          ${backgroundColor ? '-highlight' : ''}
          ${props.shouldTacticHaveSelfRespect ? '-with-self-respect' : ''}
        `}
        tactic={props.cell.tactic}
        shardId={props.cell.shardId}
        onClick={onClick}
        circleEl={
          hasChildrenBoxes &&
          (isBoxHidden ?
          <button type="button" className="show-boxes">⛶</button> :
          <button type="button" className="hide-boxes">▬</button>)
        }
      />
    </>
  );
};

export default TacticNodeForHypothesis;
