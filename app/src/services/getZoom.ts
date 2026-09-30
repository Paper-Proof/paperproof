/*
  [Claude comment]
  We zoom .proof-tree with CSS `zoom` rather than `transform: scale()`: a transform only shrinks
  the painted tree, its layout box keeps the unscaled size - so zooming out left a blank strip
  to the right of (and below) the proof. `zoom` resizes the layout box too.
*/
const getZoom = (proofTreeEl: HTMLElement): number =>
  parseFloat(getComputedStyle(proofTreeEl).zoom) || 1;

export default getZoom;
