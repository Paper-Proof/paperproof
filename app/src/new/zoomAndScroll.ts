

const zoomAndScroll = (event: React.MouseEvent<HTMLElement>) => {
  event.stopPropagation();
  const box = event.currentTarget.closest('.box') as HTMLElement;
  if (!box) return

  const scaleFactor = Math.min(
    window.innerWidth / box.offsetWidth,
    window.innerHeight / box.offsetHeight
  );

  const rootEl = document.getElementById("root")!;
  const htmlEl = document.getElementsByTagName("html")[0]!;
  const initialScale = parseFloat(getComputedStyle(rootEl).transform.split(',')[3]) || 1;
  const initialScrollTop = htmlEl.scrollTop;
  const initialScrollLeft = htmlEl.scrollLeft;

  const predictedBoxTop = box.offsetTop * scaleFactor;
  const predictedBoxLeft = box.offsetLeft * scaleFactor;
  const scrollTopEnd = (predictedBoxTop + box.offsetHeight * scaleFactor / 2) - window.innerHeight / 2;
  const scrollLeftEnd = (predictedBoxLeft + box.offsetWidth * scaleFactor / 2) - window.innerWidth / 2;
  
  const animationLength = 300;
  const start = performance.now();
  const scaleIncrement = (scaleFactor - initialScale) / animationLength;
  const scrollTopIncrement = (scrollTopEnd - initialScrollTop) / animationLength;
  const scrollLeftIncrement = (scrollLeftEnd - initialScrollLeft) / animationLength;

  function step() {
    const elapsed = performance.now() - start;

    if (elapsed < animationLength) {
      rootEl.style.transform = `scale(${initialScale + scaleIncrement * elapsed})`;
      htmlEl.scrollTop = initialScrollTop + scrollTopIncrement * elapsed;
      htmlEl.scrollLeft = initialScrollLeft + scrollLeftIncrement * elapsed;
      window.requestAnimationFrame(step);
    } else {
      rootEl.style.transform = `scale(${scaleFactor})`;
      htmlEl.scrollTop = scrollTopEnd;
      htmlEl.scrollLeft = scrollLeftEnd;
    }
  }
  
  window.requestAnimationFrame(step);
}

export default zoomAndScroll;
