import { Arrow, Point } from 'types';
import distance from './distance';

const createArrow = (from: string | HTMLElement | null, to: string | HTMLElement | null) : Arrow | null => {
  const proofTreeEl = document.getElementsByClassName("proof-tree")[0] as HTMLElement;
  const fromEl = typeof from === 'string' ? document.getElementById(from) : from;
  const toEl = typeof to === 'string' ? document.getElementById(to) : to;
  if (!proofTreeEl || !fromEl || !toEl) return null;

  const currentZoom = parseFloat(getComputedStyle(proofTreeEl).transform.split(',')[3]) || 1;

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
