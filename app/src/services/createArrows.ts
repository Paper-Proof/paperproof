import { Arrow, ConvertedProofTree, Point } from 'types';
import distance from './distance';

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
          x: distance('left', fromEl, proofTreeEl)/currentZoom + fromEl.offsetWidth/2,
          y: distance('top', fromEl, proofTreeEl)/currentZoom + fromEl.offsetHeight
        };

        const pointTo : Point = {
          x: distance('left', toEl, proofTreeEl)/currentZoom + toEl.offsetWidth/2,
          y: distance('top', toEl, proofTreeEl)/currentZoom
        };

        perfectArrows.push({ from: pointFrom, to: pointTo });
      });
    });
  });

  return perfectArrows;
}

export default createArrows;
