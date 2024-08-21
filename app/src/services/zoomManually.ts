const zoomManually = (type: "in" | "out") => {
  const proofTreeEl = document.getElementsByClassName("proof-tree")[0] as HTMLElement;
  if (!proofTreeEl) return;
  const initialScale = parseFloat(getComputedStyle(proofTreeEl).transform.split(',')[3]) || 1;
  proofTreeEl.style.transition = 'transform 0.2s';
  const increment = type === "in" ? 0.1 : -0.1;
  proofTreeEl.style.transform = `scale(${initialScale + increment})`;
  setTimeout(() => {
    proofTreeEl.style.transition = '';
  }, 200);
};

export default zoomManually;
