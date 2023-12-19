const distanceTop = (el1: HTMLElement, el2: HTMLElement) => {
  const rect1 = el1.getBoundingClientRect();
  const rect2 = el2.getBoundingClientRect();
  return Math.abs(rect1.top - rect2.top);
}

const distanceLeft = (el1: HTMLElement, el2: HTMLElement) => {
  const rect1 = el1.getBoundingClientRect();
  const rect2 = el2.getBoundingClientRect();
  return Math.abs(rect1.left - rect2.left);
}

const zoomAndScroll = (event: React.MouseEvent<HTMLElement>) => {
  event.stopPropagation();
  const htmlEl = document.getElementsByTagName("html")[0];
  const proofTreeEl = document.getElementsByClassName("proof-tree")[0] as HTMLElement;
  const boxEl = event.currentTarget.closest(".box") as HTMLElement;
  if (!htmlEl || !proofTreeEl || !boxEl) return;
  const initialScale = parseFloat(getComputedStyle(proofTreeEl).transform.split(',')[3]) || 1;

  // We can make the content look smaller, but can't make it look bigger - max zoom is 1
  const scaleFactorWantedOld = Math.min(
    window.innerWidth / boxEl.offsetWidth, 
    window.innerHeight / boxEl.offsetHeight // .offsetHeight ignores transforms
  );
  const scaleFactorWanted = window.innerWidth / boxEl.offsetWidth;
  const scaleFactor = Math.min(scaleFactorWanted, 1)

  const scrollTopFinal_top =
    distanceTop(htmlEl, proofTreeEl) +
    distanceTop(proofTreeEl, boxEl) / initialScale * scaleFactor;
  const scrollTopFinal = scrollTopFinal_top - (
    window.innerHeight/2 - boxEl.offsetHeight * scaleFactor / 2
  );

  const scrollLeftFinal_left =
    distanceLeft(proofTreeEl, htmlEl) +
    distanceLeft(proofTreeEl, boxEl) / initialScale * scaleFactor;
  const scrollLeftFinal = scrollLeftFinal_left - (
    window.innerWidth/2 - boxEl.offsetWidth * scaleFactor / 2
  );

  const initialScrollTop = htmlEl.scrollTop;
  const initialScrollLeft = htmlEl.scrollLeft;

  const animationLength = 300; // 300ms
  const start = performance.now();
  const scalePerMs = (scaleFactor - initialScale) / animationLength;
  const scrollTopPerMs = (scrollTopFinal - initialScrollTop) / animationLength;
  const scrollLeftPerMs = (scrollLeftFinal - initialScrollLeft) / animationLength;

  // This is a "oh, we're past the deadline again!" animation -
  // every time the browser allows us to update our UI (so every time `window.requestAnimationFrame` is called),
  // we look at how much time has passed since the beginning of the animation, and progress the appropriate amount.
  const step = () => {
    const elapsed = performance.now() - start;

    if (elapsed < animationLength) {
      proofTreeEl.style.transform = `scale(${initialScale + scalePerMs * elapsed})`;
      htmlEl.scrollTop = initialScrollTop + scrollTopPerMs * elapsed;
      htmlEl.scrollLeft = initialScrollLeft + scrollLeftPerMs * elapsed;
      window.requestAnimationFrame(step);
    } else {
      proofTreeEl.style.transform = `scale(${scaleFactor})`;
      htmlEl.scrollTop = scrollTopFinal;
      htmlEl.scrollLeft = scrollLeftFinal;
    }
  }

  window.requestAnimationFrame(step);
}

export default zoomAndScroll;
