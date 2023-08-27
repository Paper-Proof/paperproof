import { UIHypTree } from 'types';

import sum from './sum';

const getTreeWidth = (hMargin: number, t: UIHypTree): number => {
  const widths = t.nodes.flatMap(n =>
    [Math.max(n.node.size[0], n.tree ? getTreeWidth(hMargin, n.tree) : 0)])
  return Math.max(t.tactic.size[0], sum(widths, hMargin));
}

export default getTreeWidth;
