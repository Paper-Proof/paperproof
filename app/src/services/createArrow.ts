import { Arrow, Point } from 'types';
import distance from './distance';
import getZoom from './getZoom';

const createArrow = (proofTreeEl: HTMLElement | null, from: string | HTMLElement | null, to: string | HTMLElement | null) : Arrow | null => {
  if (!proofTreeEl) return null;
  const find = (x: string | HTMLElement | null) =>
    typeof x === 'string' ? proofTreeEl.querySelector<HTMLElement>(`#${CSS.escape(x)}`) : x;
  const fromEl = find(from);
  const toEl = find(to);
  if (!fromEl || !toEl) return null;

  const zoom = getZoom(proofTreeEl);
  const scale = proofTreeEl.getBoundingClientRect().width / parseFloat(getComputedStyle(proofTreeEl).width);
  if (!scale) return null;
  const currentZoom = Math.abs(scale - zoom) < 0.001 ? zoom : scale;

  const fromRect = fromEl.getBoundingClientRect();
  const toRect = toEl.getBoundingClientRect();
  const isTouching = toRect.top >= fromRect.top && toRect.top <= fromRect.bottom + 1 && toRect.left < fromRect.right && fromRect.left < toRect.right;
  if (isTouching) return null;

  const pointFrom : Point = {
    x: distance('left', fromEl, proofTreeEl)/currentZoom + fromEl.offsetWidth/2,
    // "- 1" is here to make the start of the arrow closer to the hypothesis node (it's prettier like this)
    y: distance('top', fromEl, proofTreeEl)/currentZoom + fromEl.offsetHeight - 1
  };

  const pointTo : Point = {
    x: distance('left', toEl, proofTreeEl)/currentZoom + toEl.offsetWidth/2,
    y: distance('top', toEl, proofTreeEl)/currentZoom
  };

  return { from: pointFrom, to: pointTo };
}

export default createArrow;
