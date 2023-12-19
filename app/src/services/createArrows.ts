import { Arrow, ConvertedProofTree, Point } from 'types';

const distanceTop = (el1: HTMLElement, el2: HTMLElement) => {
  const rect1 = el1.getBoundingClientRect();
  const rect2 = el2.getBoundingClientRect();
  return Math.abs(rect1.top - rect2.top);
}

const distanceLeft = (el1: HTMLElement, el2: HTMLElement) => {
  const rect1 = el1.getBoundingClientRect();
  const rect2 = el2.getBoundingClientRect();
  return Math.abs(rect1.left - rect2.left);
}

const createArrows = (proofTree : ConvertedProofTree) : Arrow[] => {
  let perfectArrows: Arrow[] = [];

  proofTree.boxes.forEach((box) => {
    box.hypTables.forEach((table) => {
      table.tabledTactics.forEach((tabledTactic) => {
        if (!tabledTactic.arrowFrom) return
        const proofTreeEl = document.getElementsByClassName("proof-tree")[0] as HTMLElement;
        const fromId = `hypothesis-${tabledTactic.arrowFrom}`;
        const toId = `tactic-${tabledTactic.tactic.id}-${tabledTactic.shardId}`;
        const fromEl = document.getElementById(fromId);
        const toEl = document.getElementById(toId);
        if (!proofTreeEl || !fromEl || !toEl) return;

        const currentZoom = parseFloat(getComputedStyle(proofTreeEl).transform.split(',')[3]) || 1;

        const pointFrom : Point = {
          x: distanceLeft(fromEl, proofTreeEl)/currentZoom + fromEl.offsetWidth/2,
          y: distanceTop(fromEl, proofTreeEl)/currentZoom + fromEl.offsetHeight
        };

        const pointTo : Point = {
          x: distanceLeft(toEl, proofTreeEl)/currentZoom + toEl.offsetWidth/2,
          y: distanceTop(toEl, proofTreeEl)/currentZoom
        };

        perfectArrows.push({ from: pointFrom, to: pointTo });
      });
    });
  });

  return perfectArrows;
}

export default createArrows;
