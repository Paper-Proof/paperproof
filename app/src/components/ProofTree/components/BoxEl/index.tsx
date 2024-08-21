import React from "react";

import { ConvertedProofTree, Box, Tactic, ContextMenuType } from "types";
import Hypotheses from "./components/Hypotheses";

import zoomToBox from '../../services/zoomToBox';
import TacticNode from "../../../TacticNode";

import { useGlobalContext } from "src/indexBrowser";
import ContextMenu from "./components/ContextMenu";
import prettifyGoalUsername from "./services/prettifyGoalUsername";
import onContextMenu from "./services/onContextMenu";
import Header from "./components/Header";
import GoalNode from "./components/GoalNode";

interface MyProps {
  box: Box;
}

const getGoalTactic = (proofTree: ConvertedProofTree, goalNodeId: string) : Tactic | undefined => {
  const goalTactic = proofTree.tactics.find((tactic) => tactic.goalArrows.find((goalArrow) => goalArrow.fromId === goalNodeId));

  const successTactic = proofTree.tactics.find((tactic) => tactic.successGoalId === goalNodeId);

  return goalTactic || successTactic;
}

interface HeaderYes {
  ifHoistUp: true;
  paddingBottomType: "small" | "big";
}
interface HeaderNo {
  ifHoistUp: false
}
export type HeaderInfo = HeaderYes | HeaderNo

const getHeader = (box: Box): HeaderInfo => {
  const isRootBox = box.id === "1"
  if (!isRootBox) return { ifHoistUp: false }
  const firstTable = box.hypTables[0]
  if (!firstTable) return { ifHoistUp: false }
  const initShard = firstTable.tabledTactics.find((tt) => tt.tactic.text === 'init')
  if (!initShard) return { ifHoistUp: false }

  const ifDirectChild = firstTable.tabledTactics.some((tt) => tt.row === 2 && tt.columnFrom < initShard.columnTo)

  return {
    ifHoistUp: true,
    paddingBottomType: ifDirectChild ? "small" : "big"
  }
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

  const { collapsedBoxIds } = useGlobalContext();
  const isCollapsed = collapsedBoxIds.find((id) => props.box.id === id);
  
  const tableWithHeader = props.box.hypTables.find((hypTable) => hypTable.row1Hyps)

  const isRootBox = props.box.id === "1"

  const headerInfo = getHeader(props.box)

  return <section
    className="box"
    id={`box-${props.box.id}`}
    onClick={onClick}
    onContextMenu={(event) => onContextMenu(event, contextMenu, setContextMenu)}
  >
    <ContextMenu box={props.box} contextMenu={contextMenu} setContextMenu={setContextMenu}/>

    {
      isRootBox &&
      <Header row1Hyps={tableWithHeader?.row1Hyps} headerInfo={headerInfo}/>
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
            <GoalNode goalNode={goalNode}/>
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
