import React from "react";
import Hint from "../../Hint";
import { ContextMenuType, HypNode } from "types";
import { useGlobalContext } from "src/indexBrowser";
import prettifyHypothesisUsername from "src/services/prettifyHypothesisUsername";
import Search from "src/components/Search";
import Menu from '@mui/material/Menu';
import MenuItem from '@mui/material/MenuItem';
import onContextMenu from "src/services/onContextMenu";

export interface HypothesisProps {
  hypNode: HypNode;
  withId?: boolean
}

const HypothesisNode = ({ withId = true, ...props }: HypothesisProps) => {
  const global = useGlobalContext();
  const [contextMenu, setContextMenu] = React.useState<ContextMenuType>(null);

  const name = prettifyHypothesisUsername(props.hypNode.name);

  const isSearched = global.searchedHypIds.find((searchedId) => props.hypNode.id === searchedId);
  const isHypHidden = name && global.deletedHypothesisNames.includes(name);

  const handleHideHypothesis = (event: React.MouseEvent) => {
    event.stopPropagation();
    if (!name) return;

    if (isHypHidden) {
      global.setDeletedHypothesisNames(global.deletedHypothesisNames.filter((n) => n !== name));
    } else {
      global.setDeletedHypothesisNames([...global.deletedHypothesisNames, name]);
    }
    setContextMenu(null);
    global.refreshUI();
  };

  const handleCloseMenu = (event: React.MouseEvent) => {
    event.stopPropagation();
    setContextMenu(null);
  };

  return(
    <Search hypNode={props.hypNode}>
      <div
        id={withId ? `hypothesis-${props.hypNode.id}` : undefined}
        className={`
          hypothesis
          -hint
          ${global.highlights?.hypIds.includes(props.hypNode.id) ? "-highlighted" : ""}
          ${props.hypNode.isProof}
          ${isSearched ? '-is-searched' : ''}
          ${isHypHidden ? '-hidden' : ''}
        `}
        onClick={(e) => isHypHidden ? handleHideHypothesis(e) : () => {}}
        onContextMenu={(event) => onContextMenu(event, contextMenu, setContextMenu)}
      >
        <Menu
          open={contextMenu !== null}
          onClose={handleCloseMenu}
          anchorReference="anchorPosition"
          anchorPosition={
            contextMenu !== null
              ? { top: contextMenu.mouseY, left: contextMenu.mouseX }
              : undefined
          }
        >
          <MenuItem onClick={handleHideHypothesis}>
            {isHypHidden ? "Show hypothesis" : "Hide hypothesis"}
          </MenuItem>
        </Menu>

        <Hint>{props.hypNode}</Hint>
        {name && <span className="name">{name}</span>}
        {!isHypHidden && name && ": "}
        {!isHypHidden && <span className="text">{props.hypNode.text}</span>}
      </div>
    </Search>
  )
};

export default HypothesisNode
