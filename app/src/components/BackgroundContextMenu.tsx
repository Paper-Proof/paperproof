import React from "react";

import { ContextMenuType } from "types";
import { useGlobalContext } from "src/indexBrowser";
import ContextMenu from "./ProofTree/components/BoxEl/components/ContextMenu";
import onContextMenu from "src/services/onContextMenu";

/*
  The proof only takes up as much room as it needs, so most of the panel is usually empty body.
  That area is outside React's root container, so it needs a listener on the document itself.
  Everything inside the tree sits in a .box, and those bring up their own menus.
*/
const BackgroundContextMenu = () => {
  const { proofTree } = useGlobalContext();
  const [contextMenu, setContextMenu] = React.useState<ContextMenuType>(null);

  React.useEffect(() => {
    const handleContextMenu = (event: MouseEvent) => {
      const target = event.target as HTMLElement;
      if (target.closest(".box")) return;
      onContextMenu(event, contextMenu, setContextMenu);
    };

    document.addEventListener("contextmenu", handleContextMenu);
    return () => document.removeEventListener("contextmenu", handleContextMenu);
  }, [contextMenu]);

  const rootBox = proofTree.boxes.find((box) => box.parentId === null);
  if (!rootBox) return null;

  return <ContextMenu box={rootBox} contextMenu={contextMenu} setContextMenu={setContextMenu}/>;
}

export default BackgroundContextMenu;
