import { HypTree, Element } from '../../../types';

import hStack from './hStack';
import vStack from './vStack';

const byLevel = (hMargin: number, trees: HypTree[]) : Element[][] => {
  const rows: Element[][] = [];
  function visit(t: HypTree) {
    while (rows.length <= t.level) {
      rows.push([]);
    }
    rows[t.level].push(vStack(0, [t.tactic, hStack(hMargin, t.nodes.map(n => n.node))]));
    for (const n of t.nodes) {
      if (n.tree) {
        visit(n.tree);
      }
    }
  }
  trees.forEach(visit);
  return rows;
}

export default byLevel;
