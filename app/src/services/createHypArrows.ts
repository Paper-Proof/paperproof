import { Arrow, ConvertedProofTree, Point } from 'types';
import createArrow from './createArrow';

const createHypArrows = (proofTree : ConvertedProofTree) : Arrow[] => {
  let perfectArrows: Arrow[] = [];

  proofTree.boxes.forEach((box) => {
    box.hypTables.forEach((table) => {
      table.tabledTactics.forEach((tabledTactic) => {
        if (!tabledTactic.arrowFrom) return
        const fromId = `hypothesis-${tabledTactic.arrowFrom}`;
        const toId = `tactic-${tabledTactic.tactic.id}-${tabledTactic.shardId}`;
        const arrow = createArrow(fromId, toId);
        if (arrow) {
          perfectArrows.push(arrow);
        }
      });
    });
  });

  return perfectArrows;
}

export default createHypArrows;
