const FLASH_CLASS = '-just-jumped-to';
const FLASH_MS = 2000;

/*
  Arrows are absolutely positioned children of a tactic, but their coordinates are measured
  against .proof-tree - which works only as long as no tactic is a containing block.
  FLASH_CLASS makes one `position: relative` for the duration of the pulse, so for those 2s
  we hand the arrows the offset they need to stay put.
*/
const setArrowOffset = (el: HTMLElement) => {
  const tree = el.closest('.proof-tree') as HTMLElement | null;
  if (!tree) return;

  const zoom = parseFloat(getComputedStyle(tree).transform.split(',')[3]) || 1;
  const treeRect = tree.getBoundingClientRect();
  const elRect = el.getBoundingClientRect();

  // Rects are scaled by the zoom, client borders aren't
  const dx = (treeRect.left - elRect.left) / zoom + tree.clientLeft - el.clientLeft;
  const dy = (treeRect.top - elRect.top) / zoom + tree.clientTop - el.clientTop;

  el.style.setProperty('--flash-dx', `${dx}px`);
  el.style.setProperty('--flash-dy', `${dy}px`);
};

const clearArrowOffset = (el: HTMLElement) => {
  el.style.removeProperty('--flash-dx');
  el.style.removeProperty('--flash-dy');
};

// [Claude comment] without this, a reflash within FLASH_MS gets cut short by the previous
// call's pending reset - so clicking twice in a row showed a pulse that died instantly.
const pendingResets = new WeakMap<HTMLElement, ReturnType<typeof setTimeout>>();

// Pulses a ring around an element (see `.-just-jumped-to` in index.css)
const flashElement = (el: Element) => {
  const htmlEl = el as HTMLElement;

  const pending = pendingResets.get(htmlEl);
  if (pending) { clearTimeout(pending); }

  htmlEl.classList.remove(FLASH_CLASS);
  clearArrowOffset(htmlEl);
  // Forcing a reflow is what lets the animation restart when it's already running
  void htmlEl.offsetWidth;
  setArrowOffset(htmlEl);
  htmlEl.classList.add(FLASH_CLASS);
  pendingResets.set(htmlEl, setTimeout(() => {
    pendingResets.delete(htmlEl);
    htmlEl.classList.remove(FLASH_CLASS);
    clearArrowOffset(htmlEl);
  }, FLASH_MS));
};

export default flashElement;
