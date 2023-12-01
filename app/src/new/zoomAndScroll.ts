import scrollIntoView from 'smooth-scroll-into-view-if-needed';

const zoomAndScroll = (event: React.MouseEvent<HTMLElement>) => {
  event.stopPropagation();
  const box = event.currentTarget.closest('.box') as HTMLElement;
  if (!box) return
  const animationLength = 300;
  const updateEveryNMs = 3;
  // 1. calculate final destination of scrolling (as if scaling is already applied!)
  const scaleFactor = Math.min(
    window.innerWidth / box.offsetWidth,
    window.innerHeight / box.offsetHeight
  );
  const predictedBoxTop = box.offsetTop * scaleFactor;
  const predictedBoxLeft = box.offsetLeft * scaleFactor;

  // 2. update both scaling and scrolling every updateEveryNMs ms during animationLength ms
  const rootEl = document.getElementById("root")!;
  const htmlEl = document.getElementsByTagName("html")[0]!;
  const initialScale = parseFloat(getComputedStyle(rootEl).transform.split(',')[3]) || 1;
  const initialScrollTop = htmlEl.scrollTop;
  const initialScrollLeft = htmlEl.scrollLeft;
  const scaleIncrement = (scaleFactor - initialScale) / (animationLength / updateEveryNMs);


  const totalUpdates = Math.ceil(animationLength / updateEveryNMs);
  const scrollTopIncrement = (predictedBoxTop - initialScrollTop) / totalUpdates;
  const scrollLeftIncrement = (predictedBoxLeft - initialScrollLeft) / totalUpdates;

  
  let i = 0;
  const intervalId = setInterval(() => {
    rootEl.style.transform = `scale(${initialScale + scaleIncrement * i})`;
    htmlEl.scrollTop = initialScrollTop + scrollTopIncrement * i;
    htmlEl.scrollLeft = initialScrollLeft + scrollLeftIncrement * i;
    i++;
    if (i >= totalUpdates) {
      clearInterval(intervalId);
      // Ensure final values are set correctly
      rootEl.style.transform = `scale(${scaleFactor})`;
      htmlEl.scrollTop = predictedBoxTop;
      htmlEl.scrollLeft = predictedBoxLeft;
    }
  }, updateEveryNMs);
}

export default zoomAndScroll;
