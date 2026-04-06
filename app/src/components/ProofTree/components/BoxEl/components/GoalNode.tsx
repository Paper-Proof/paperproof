import React from 'react';
import katex from 'katex';
import 'katex/dist/katex.min.css';
import Hint from './Hint';
import { useGlobalContext } from 'src/indexBrowser';
import { ContextMenuType, TypeGoalNode } from 'types';
import fancySubstringHypotheses from 'src/services/fancySubstringHypotheses';
import Menu from '@mui/material/Menu';
import MenuItem from '@mui/material/MenuItem';
import onContextMenu from 'src/services/onContextMenu';

const GoalNodeEl = ({ goalNode }: { goalNode: TypeGoalNode }) => {
  const global = useGlobalContext();
  const [contextMenu, setContextMenu] = React.useState<ContextMenuType>(null);
  const { latexSettings } = global;

  const latexString = latexSettings.isActive ? latexSettings.map[goalNode.text] : undefined;

  const handleCopy = (event: React.MouseEvent) => {
    event.stopPropagation();
    navigator.clipboard.writeText(goalNode.text);
    setContextMenu(null);
  };

  return (
    <div
      className={`goal -hint ${global.highlights?.goalId === goalNode.id ? "-highlighted" : ""}`}
      onContextMenu={global.isStandalone ? undefined : (event) => onContextMenu(event, contextMenu, setContextMenu)}
    >
      {!global.isStandalone && (
        <Menu
          open={contextMenu !== null}
          onClose={(event: React.MouseEvent) => { event.stopPropagation(); setContextMenu(null); }}
          anchorReference="anchorPosition"
          anchorPosition={contextMenu !== null ? { top: contextMenu.mouseY, left: contextMenu.mouseX } : undefined}
        >
          <MenuItem onClick={handleCopy}>Copy</MenuItem>
        </Menu>
      )}
      <Hint>{goalNode}</Hint>
      {latexString
        ? <div className="text" dangerouslySetInnerHTML={{ __html: katex.renderToString(latexString, { throwOnError: false, displayMode: true }) }}/>
        : <div className="text">{fancySubstringHypotheses(goalNode.text, global)}</div>
      }
    </div>
  );
};

export default GoalNodeEl;
