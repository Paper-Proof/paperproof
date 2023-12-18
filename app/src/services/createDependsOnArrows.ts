import { ConvertedProofTree } from 'types';
// @ts-ignore
import LeaderLine from './LeaderLine.min.js';

const options = {
  path: "straight",
  startSocket: "bottom",
  endSocket: "top",
  size: 3,
  hide: true
}

const createDependsOnArrows = (proofTree : ConvertedProofTree) : LeaderLine[] => {
  let leaderLines: LeaderLine[] = [];
  proofTree.tactics.forEach((tactic) => {
    const allTacticUniqueIds = Array.from(document.querySelectorAll(`[id^="tactic-${tactic.id}-"]`)).map((node) => node.id.split('-')[2]);
    tactic.dependsOnIds.forEach((dependsOnHypId) => {
      const hypEl = document.getElementById(`hypothesis-${dependsOnHypId}`);
      allTacticUniqueIds.forEach((uniqueId) => {
        const tacticEl = document.getElementById(`tactic-${tactic.id}-${uniqueId}`)
        if (!hypEl || !tacticEl) return
        const newLeaderLine = new LeaderLine(hypEl, tacticEl, options);
        leaderLines.push(newLeaderLine);
      })
    });
  });
  // TODO this is wild of course, shall fix this later
  window.leaderLines = leaderLines;
  return leaderLines;
}

export default createDependsOnArrows;
