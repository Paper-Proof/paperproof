import React from "react";
import Menu from '@mui/material/Menu';
import MenuItem from '@mui/material/MenuItem';
import { Divider, Switch } from "@mui/material";
import { useGlobalContext } from "src/indexBrowser";
import { Box, ContextMenuType, Settings } from "types";
import zoomManually from "src/services/zoomManually";

interface Props {
  box: Box;
  contextMenu: ContextMenuType;
  setContextMenu: React.Dispatch<React.SetStateAction<ContextMenuType>>;
}

const ContextMenu = (props: Props) => {
  const {
    refreshUI,
    collapsedBoxIds, setCollapsedBoxIds,
    settings,        setSettings
  } = useGlobalContext();

  const handleSettingToggle = (settingKey: keyof Settings) => (event: React.MouseEvent) => {
    event.stopPropagation();
    setSettings({ ...settings, [settingKey]: !settings[settingKey] });
    refreshUI();
  };

  const handleClose = (event: React.MouseEvent) => {
    event.stopPropagation();
    props.setContextMenu(null);
  };

  const isCollapsed = collapsedBoxIds.find((id) => props.box.id === id);

  const handleCollapse = (event: React.MouseEvent) => {
    event.stopPropagation();
    if (isCollapsed) {
      setCollapsedBoxIds(collapsedBoxIds.filter((id) => id !== props.box.id));
    } else {
      setCollapsedBoxIds([...collapsedBoxIds, props.box.id]);
    }
    props.setContextMenu(null);
    refreshUI();
  };

  const handleZoom = (event: React.MouseEvent, type: "in" | "out") => {
    event.stopPropagation();
    zoomManually(type);
  };

  return (
    <Menu
      open={props.contextMenu !== null}
      onClose={handleClose}
      anchorReference="anchorPosition"
      anchorPosition={
        props.contextMenu !== null
          ? { top: props.contextMenu.mouseY, left: props.contextMenu.mouseX }
          : undefined
      }
    >
      {
        props.box.id !== "1" &&
        <MenuItem onClick={handleCollapse}>
          {isCollapsed ? "Expand box" : "Collapse box"}
        </MenuItem>
      }
      { props.box.id !== "1" && <Divider/> }

      <MenuItem onClick={(event) => handleZoom(event, "in")}>
        <div className="text">Zoom in</div>
        <div className="shortcut">⎇ +</div>
      </MenuItem>

      <MenuItem onClick={(event) => handleZoom(event, "out")}>
        <div className="text">Zoom out</div>
        <div className="shortcut">⎇ -</div>
      </MenuItem>

      <Divider/>

      <MenuItem onClick={handleSettingToggle("isCompactMode")}>
        <div className="text">Compact horizontally</div>
        <Switch checked={settings.isCompactMode} size="small"/>
      </MenuItem>

      <MenuItem onClick={handleSettingToggle("isCompactTactics")}>
        <div className="text">Compact tactics</div>
        <Switch checked={settings.isCompactTactics} size="small"/>
      </MenuItem>

      <Divider/>

      <MenuItem onClick={handleSettingToggle("isHiddenGoalNames")}>
        <div className="text">Hide goal names</div>
        <Switch checked={settings.isHiddenGoalNames} size="small"/>
      </MenuItem>

      <MenuItem onClick={handleSettingToggle("isGreenHypotheses")}>
        <div className="text">Always green hypotheses</div>
        <Switch checked={settings.isGreenHypotheses} size="small"/>
      </MenuItem>

      <Divider/>

      <MenuItem onClick={handleSettingToggle("isReadonlyMode")}>
        <div className="text">Readonly mode</div>
        <Switch checked={settings.isReadonlyMode} size="small"/>
      </MenuItem>
    </Menu>
  )
}

export default ContextMenu;
