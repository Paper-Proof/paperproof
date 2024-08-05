import { ContextMenuType } from "types";

// Copypasted from mui docs
// (see https://mui.com/material-ui/react-menu/#context-menu code example)
const onContextMenu = (event: React.MouseEvent, contextMenu: ContextMenuType, setContextMenu: React.Dispatch<React.SetStateAction<ContextMenuType>>) => {
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

export default onContextMenu;
