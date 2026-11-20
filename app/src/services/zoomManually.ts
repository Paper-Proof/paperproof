import getZoom from "./getZoom";

const zoomManually = (proofTreeEl: HTMLElement | null, type: "in" | "out") => {
  if (!proofTreeEl) return;
  const increment = type === "in" ? 0.1 : -0.1;
  proofTreeEl.style.zoom = `${getZoom(proofTreeEl) + increment}`;
};

export default zoomManually;
