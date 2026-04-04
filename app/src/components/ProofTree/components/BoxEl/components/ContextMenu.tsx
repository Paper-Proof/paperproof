import React from "react";
import Menu from '@mui/material/Menu';
import MenuItem from '@mui/material/MenuItem';
import { Divider, Switch } from "@mui/material";
import { useGlobalContext } from "src/indexBrowser";
import { Box, ContextMenuType, Settings } from "types";
import zoomManually from "src/services/zoomManually";
import copyProofStructureForLLM from "src/services/copyProofStructureForLLM";

interface Props {
  box: Box;
  contextMenu: ContextMenuType;
  setContextMenu: React.Dispatch<React.SetStateAction<ContextMenuType>>;
}

const ContextMenu = (props: Props) => {
  const {
    createSnapshot,
    proofTree,
    refreshUI,
    collapsedBoxIds, setCollapsedBoxIds,
    settings,        setSettings,
    setConverted,
    setSnackbarMessage,
    setSnackbarOpen,
  } = useGlobalContext();

  type BooleanSettingKey = { [K in keyof Settings]: Settings[K] extends boolean ? K : never }[keyof Settings];
  const handleSettingToggle = (settingKey: BooleanSettingKey) => (event: React.MouseEvent) => {
    event.stopPropagation();
    // When we switch our modes back and forth, it's important to clear the proof tree, otherwise users will briefly see a silly "css has changed, but proof tree stays the same" state
    if (settingKey === "isSingleTacticMode") {
      setConverted(null);
    }
    setSettings({ ...settings, [settingKey]: !settings[settingKey] });
    refreshUI();
  };

  const handleClose = (event: React.MouseEvent) => {
    event.stopPropagation();
    props.setContextMenu(null);
  };

  const handleSnapshot = async (event: React.MouseEvent) => {
    event.stopPropagation();
    try {
      const url = await createSnapshot();
      navigator.clipboard.writeText(url);
      setSnackbarMessage(<div style={{ display: 'flex', alignItems: 'center' }}>
        <span style={{ paddingRight: 10 }}>📸</span>
        <span>Created a snapshot!<br/>The link is already in your clipboard.</span>
      </div>);
      setSnackbarOpen(true);
    } catch (error) {
      console.error('Failed to create snapshot:', error);
      setSnackbarMessage(`Couldn't create a snapshot! This is probably because you are in Github Codespaces. It should work locally!`);
      setSnackbarOpen(true);
    }
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

  const [zoom, setZoom] = React.useState(100);

  React.useEffect(() => {
    if (!props.contextMenu) return;
    const proofTreeEl = document.getElementsByClassName("proof-tree")[0] as HTMLElement;
    if (!proofTreeEl) return;
    const currentScale = parseFloat(getComputedStyle(proofTreeEl).transform.split(',')[3]) || 1;
    setZoom(Math.round(currentScale * 10) * 10);
  }, [props.contextMenu]);

  const copyForLLM = (event: React.MouseEvent) => {
    event.stopPropagation();
    const proofStructure = copyProofStructureForLLM(proofTree);
    navigator.clipboard.writeText(proofStructure);
    props.setContextMenu(null);
  }

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

      <MenuItem onClick={handleSettingToggle("isSingleTacticMode")}>
        <div className="text">Single-tactic Mode</div>
        <Switch checked={settings.isSingleTacticMode} size="small"/>
      </MenuItem>

      <Divider/>
      <MenuItem disableRipple className="-zoom-control">
        <div className="text">Zoom</div>
        <div className="zoom-buttons">
          <button onClick={(e) => { e.stopPropagation(); zoomManually("out"); setZoom(z => z - 10); }}>−</button>
          <span className="zoom-value">{zoom}%</span>
          <button onClick={(e) => { e.stopPropagation(); zoomManually("in"); setZoom(z => z + 10); }}>+</button>
        </div>
      </MenuItem>

      <MenuItem disableRipple className="-font-size-control">
        <div className="text">Font size</div>
        <div className="font-size-buttons">
          <button onClick={(e) => { e.stopPropagation(); setSettings({ ...settings, fontSize: settings.fontSize - 1 }); refreshUI(); }}>−</button>
          <span className="font-size-value">{settings.fontSize}px</span>
          <button onClick={(e) => { e.stopPropagation(); setSettings({ ...settings, fontSize: settings.fontSize + 1 }); refreshUI(); }}>+</button>
        </div>
      </MenuItem>
      
      {
        !settings.isSingleTacticMode &&
        <>
          <Divider/>

          <MenuItem onClick={handleSettingToggle("isCompactMode")}>
            <div className="text">Compact horizontally</div>
            <Switch checked={settings.isCompactMode} size="small"/>
          </MenuItem>

          <MenuItem onClick={handleSettingToggle("isCompactTactics")}>
            <div className="text">Compact tactics</div>
            <Switch checked={settings.isCompactTactics} size="small"/>
          </MenuItem>
        </>
      }

      <Divider/>

      <MenuItem onClick={handleSettingToggle("isHiddenGoalNames")}>
        <div className="text">Hide goal names</div>
        <Switch checked={settings.isHiddenGoalNames} size="small"/>
      </MenuItem>

      <MenuItem onClick={handleSettingToggle("isGreenHypotheses")}>
        <div className="text">Make all hypotheses green</div>
        <Switch checked={settings.isGreenHypotheses} size="small"/>
      </MenuItem>

      {
        settings.isSingleTacticMode &&
        <MenuItem onClick={handleSettingToggle("areHypsHighlighted")}>
          <div className="text">Should highlight hypothesis names</div>
          <Switch checked={settings.areHypsHighlighted} size="small"/>
        </MenuItem>
      }

      <MenuItem onClick={copyForLLM}>
        <div className="text">Copy for LLM</div>
        <div className="shortcut" style={{ textAlign: 'center' }}>📋</div>
      </MenuItem>

      <MenuItem onClick={handleSnapshot}>
        <div className="text">Create snapshot</div>
        <div className="shortcut" style={{ textAlign: 'center' }}>📸</div>
      </MenuItem>
    </Menu>
  )
}

export default ContextMenu;
