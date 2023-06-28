import { HypTree } from '../../types';

import sum from './sum';

export default function getTreeWidth(hMargin: number, t: HypTree): number {
  const widths = t.nodes.flatMap(n =>
    [Math.max(n.node.size[0], n.tree ? getTreeWidth(hMargin, n.tree) : 0)])
  return Math.max(t.tactic.size[0], sum(widths, hMargin));
}
