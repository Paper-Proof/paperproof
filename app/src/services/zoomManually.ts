import getZoom from "./getZoom";

const zoomManually = (type: "in" | "out") => {
  const proofTreeEl = document.getElementsByClassName("proof-tree")[0] as HTMLElement;
  if (!proofTreeEl) return;
  const increment = type === "in" ? 0.1 : -0.1;
  proofTreeEl.style.zoom = `${getZoom(proofTreeEl) + increment}`;
};

export default zoomManually;
