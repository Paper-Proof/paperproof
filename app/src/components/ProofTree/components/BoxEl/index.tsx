import React from "react";

import { ConvertedProofTree, Box, Tactic, ContextMenuType } from "types";
import Hypotheses from "./components/Hypotheses";
import Hint from "./components/Hint";

import zoomToBox from '../../services/zoomToBox';
import TacticNode from "../../../TacticNode";

import { useGlobalContext } from "src/indexBrowser";
import ContextMenu from "./components/ContextMenu";
import prettifyGoalUsername from "./utils/prettifyGoalUsername";
import onContextMenu from "./utils/onContextMenu";
import Header from "./components/Header";

interface MyProps {
  box: Box;
}

const getGoalTactic = (proofTree: ConvertedProofTree, goalNodeId: string) : Tactic | undefined => {
  const goalTactic = proofTree.tactics.find((tactic) => tactic.goalArrows.find((goalArrow) => goalArrow.fromId === goalNodeId));

  const successTactic = proofTree.tactics.find((tactic) => tactic.successGoalId === goalNodeId);

  return goalTactic || successTactic;
}

const BoxEl = (props: MyProps) => {
  const [contextMenu, setContextMenu] = React.useState<ContextMenuType>(null);
  const { proofTree } = useGlobalContext();

  const childrenBoxes = proofTree.boxes.filter((box) => box.parentId === props.box.id);

  const onClick = (event: React.MouseEvent<HTMLElement>) => {
    event.stopPropagation();
    localStorage.setItem('zoomedBoxId', props.box.id);
    zoomToBox(props.box.id);
  }

  const { collapsedBoxIds, highlights } = useGlobalContext();
  const isCollapsed = collapsedBoxIds.find((id) => props.box.id === id);
  
  const tableWithHeader = props.box.hypTables.find((hypTable) => hypTable.header)
  const header = tableWithHeader && tableWithHeader.header

  const isRootBox = props.box.id === "1"

  return <section
    className="box"
    id={`box-${props.box.id}`}
    onClick={onClick}
    onContextMenu={(event) => onContextMenu(event, contextMenu, setContextMenu)}
  >
    <ContextMenu box={props.box} contextMenu={contextMenu} setContextMenu={setContextMenu}/>

    {
      isRootBox &&
      <Header header={header}/>
    }

    {!isCollapsed &&
      <div className="box-insides">
        <Hypotheses hypTables={props.box.hypTables}/>

        {
          childrenBoxes.length > 0 &&
          <div className="child-boxes">
            {childrenBoxes.map((childBox) =>
              <BoxEl key={childBox.id} box={childBox}/>
            )}
          </div>
        }

        {props.box.goalNodes.slice().reverse().map((goalNode) =>
          <div className="goals" key={goalNode.id}>
            {
              getGoalTactic(proofTree, goalNode.id) ?
                <TacticNode tactic={getGoalTactic(proofTree, goalNode.id)!}/> :
                <div className="tactic -ellipsis">...</div>
            }
            <div className={`goal -hint ${!highlights || highlights.goalId === goalNode.id ? "" : "-faded"}`}>
              <Hint>{goalNode}</Hint>
              {goalNode.text}
            </div>
          </div>
        )}
      </div>
    }

    {
      isRootBox ?
      <footer>
        <div className="title">theorem</div>
      </footer> :
      <div className="goal-username">
        {prettifyGoalUsername(props.box.goalNodes[0].name)}
      </div>
    }
  </section>
}

export default BoxEl;
