import React, { useContext } from "react";

import { ConvertedProofTree, Box, HypNode, Highlights, Tactic } from "types";
import Hypotheses from "./components/Hypotheses";
import Hint from "./components/Hint";

import zoomToBox from '../../services/zoomToBox';
import TacticNode from "../../../TacticNode";

import Menu from '@mui/material/Menu';
import MenuItem from '@mui/material/MenuItem';
import { GlobalContext } from "src/indexBrowser";

interface MyProps {
  box: Box;
  proofTree: ConvertedProofTree;
  highlights: Highlights
}

const getGoalTactic = (proofTree: ConvertedProofTree, goalNodeId: string) : Tactic | undefined => {
  const goalTactic = proofTree.tactics.find((tactic) => tactic.goalArrows.find((goalArrow) => goalArrow.fromId === goalNodeId));

  const successTactic = proofTree.tactics.find((tactic) => tactic.successGoalId === goalNodeId);

  return goalTactic || successTactic;
}

// "a._@.Mathlib.Init.Algebra.Order._hyg.1764" => "a"
// (https://github.com/leanprover/lean4/blob/d37bbf4292c72798afdff8bf5488df09193fde58/src/Init/Prelude.lean#L4132)
// Note: I was doing this in the parser with `.eraseMacroScopes`, but we depend in hygienic goal usernames, might be dangerous - so I moved it here.
const prettifyGoalUsername = (username : string) => {
  return username.split('._@')[0];
}

const BoxEl = (props: MyProps) => {
  const [contextMenu, setContextMenu] = React.useState<{
    mouseX: number;
    mouseY: number;
  } | null>(null);
  const [collapsed, setCollapsed] = React.useState<boolean>(false);

  const { refreshUI } = useContext(GlobalContext);

  const handleContextMenu = (event: React.MouseEvent) => {
    event.preventDefault();
    event.stopPropagation();
    setContextMenu(
      contextMenu === null
        ? {
            mouseX: event.clientX + 2,
            mouseY: event.clientY - 6,
          }
        : // repeated contextmenu when it is already open closes it with Chrome 84 on Ubuntu
          // Other native context menus might behave different.
          // With this behavior we prevent contextmenu from the backdrop to re-locale existing context menus.
          null,
    );
  };

  const handleClose = (event: React.MouseEvent) => {
    event.stopPropagation();
    setContextMenu(null);
  };

  const handleCollapse = (event: React.MouseEvent) => {
    event.stopPropagation();
    setCollapsed(!collapsed);
    setContextMenu(null);
    refreshUI();
  };

  const handleZoom = (event: React.MouseEvent, type: "in" | "out") => {
    event.stopPropagation();

    const proofTreeEl = document.getElementsByClassName("proof-tree")[0] as HTMLElement;
    if (!proofTreeEl) return;
    const initialScale = parseFloat(getComputedStyle(proofTreeEl).transform.split(',')[3]) || 1;
    proofTreeEl.style.transition = 'transform 0.2s';
    const increment = type === "in" ? 0.1 : -0.1;
    proofTreeEl.style.transform = `scale(${initialScale + increment})`;
    setTimeout(() => {
      proofTreeEl.style.transition = '';
    }, 200);
  }

  const handleCompactMode = (event: React.MouseEvent) => {
    event.stopPropagation();
    const proofTreeEl = document.getElementsByClassName("proof-tree")[0] as HTMLElement;
    if (!proofTreeEl) return;
    proofTreeEl.classList.toggle('-compact');
    refreshUI();
    setContextMenu(null);
  };

  const childrenBoxes = props.proofTree.boxes.filter((box) => box.parentId === props.box.id);

  const onClick = (event: React.MouseEvent<HTMLElement>) => {
    event.stopPropagation();
    localStorage.setItem('zoomedBoxId', props.box.id);
    zoomToBox(props.box.id);
  }

  return <section className="box" id={`box-${props.box.id}`} onClick={onClick} onContextMenu={handleContextMenu}>
    <Menu
      open={contextMenu !== null}
      onClose={handleClose}
      anchorReference="anchorPosition"
      anchorPosition={
        contextMenu !== null
          ? { top: contextMenu.mouseY, left: contextMenu.mouseX }
          : undefined
      }
    >
      <MenuItem onClick={handleCollapse}>{collapsed ? "Expand" : "Collapse"}</MenuItem>
      <MenuItem onClick={(event) => handleZoom(event, "in")}>Zoom In</MenuItem>
      <MenuItem onClick={(event) => handleZoom(event, "out")}>Zoom Out</MenuItem>
      <MenuItem onClick={handleCompactMode}>Compact mode</MenuItem>
      <MenuItem onClick={handleClose}>Close</MenuItem>
    </Menu>

    {!collapsed &&
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
                <TacticNode tactic={getGoalTactic(props.proofTree, goalNode.id)}/> :
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
      {prettifyGoalUsername(props.box.goalNodes[0].name)}
    </div>
  </section>
}

export default BoxEl;
