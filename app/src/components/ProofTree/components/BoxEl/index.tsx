import React, { useContext } from "react";

import { ConvertedProofTree, Box, Highlights, Tactic } from "types";
import Hypotheses from "./components/Hypotheses";
import Hint from "./components/Hint";

import zoomToBox from '../../services/zoomToBox';
import TacticNode from "../../../TacticNode";

import { GlobalContext } from "src/indexBrowser";
import ContextMenu from "./components/ContextMenu";
import prettifyGoalUsername from "./utils/prettifyGoalUsername";

interface MyProps {
  box: Box;
  proofTree: ConvertedProofTree;
  highlights: Highlights;
}

const getGoalTactic = (proofTree: ConvertedProofTree, goalNodeId: string) : Tactic | undefined => {
  const goalTactic = proofTree.tactics.find((tactic) => tactic.goalArrows.find((goalArrow) => goalArrow.fromId === goalNodeId));

  const successTactic = proofTree.tactics.find((tactic) => tactic.successGoalId === goalNodeId);

  return goalTactic || successTactic;
}

const BoxEl = (props: MyProps) => {
  const [contextMenu, setContextMenu] = React.useState<{
    mouseX: number;
    mouseY: number;
  } | null>(null);

  // Copypasted from mui docs
  // (see https://mui.com/material-ui/react-menu/#context-menu code example)
  const handleContextMenu = (event: React.MouseEvent) => {
    event.preventDefault();
    event.stopPropagation();
    setContextMenu(
      contextMenu === null ?
      {
        mouseX: event.clientX + 2,
        mouseY: event.clientY - 6,
      }
      : null,
    );
  };

  const childrenBoxes = props.proofTree.boxes.filter((box) => box.parentId === props.box.id);

  const onClick = (event: React.MouseEvent<HTMLElement>) => {
    event.stopPropagation();
    localStorage.setItem('zoomedBoxId', props.box.id);
    zoomToBox(props.box.id);
  }

  const { collapsedBoxIds } = useContext(GlobalContext);

  const isCollapsed = collapsedBoxIds.find((id) => props.box.id === id);

  return <section className="box" id={`box-${props.box.id}`} onClick={onClick} onContextMenu={handleContextMenu}>
    <ContextMenu box={props.box} contextMenu={contextMenu} setContextMenu={setContextMenu}/>

    {!isCollapsed &&
      <div className="box-insides">
        <Hypotheses proofTree={props.proofTree} hypTables={props.box.hypTables} highlights={props.highlights}/>

        {
          childrenBoxes.length > 0 &&
          <div className="child-boxes">
            {childrenBoxes.map((childBox) =>
              <BoxEl key={childBox.id} box={childBox} proofTree={props.proofTree} highlights={props.highlights}/>
            )}
          </div>
        }

        {props.box.goalNodes.slice().reverse().map((goalNode) =>
          <div className="goals" key={goalNode.id}>
            {
              getGoalTactic(props.proofTree, goalNode.id) ?
                <TacticNode tactic={getGoalTactic(props.proofTree, goalNode.id)!}/> :
                <div className="tactic -ellipsis">...</div>
            }
            <div className={`goal -hint ${!props.highlights || props.highlights.goalId === goalNode.id ? "" : "-faded"}`}>
              <Hint>{goalNode}</Hint>
              {goalNode.text}
            </div>
          </div>
        )}
      </div>
    }
    <div className="goal-username">
      {prettifyGoalUsername(props.box.goalNodes[0].name, props.box.id)}
    </div>
  </section>
}

export default BoxEl;
