

const zoomAndScroll = (event: React.MouseEvent<HTMLElement>) => {
  event.stopPropagation();
  const box = event.currentTarget.closest('.box') as HTMLElement;
  if (!box) return
  const animationLength = 300;
  const updateEveryNMs = 10;
  // 1. calculate final destination of scrolling (as if scaling is already applied!)
  const scaleFactor = Math.min(
    window.innerWidth / box.offsetWidth,
    window.innerHeight / box.offsetHeight
  );
  
  // 2. update both scaling and scrolling every updateEveryNMs ms during animationLength ms
  const rootEl = document.getElementById("root")!;
  const htmlEl = document.getElementsByTagName("html")[0]!;
  const initialScale = parseFloat(getComputedStyle(rootEl).transform.split(',')[3]) || 1;
  const initialScrollTop = htmlEl.scrollTop;
  const initialScrollLeft = htmlEl.scrollLeft;
  const scaleIncrement = (scaleFactor - initialScale) / (animationLength / updateEveryNMs);
  
  const totalUpdates = Math.ceil(animationLength / updateEveryNMs);
  // Calculate the increment for scrollTop and scrollLeft
  const predictedBoxTop = box.offsetTop * scaleFactor;
  const predictedBoxLeft = box.offsetLeft * scaleFactor;
  const scrollTopEnd = (predictedBoxTop + box.offsetHeight * scaleFactor / 2) - window.innerHeight / 2;
  const scrollLeftEnd = (predictedBoxLeft + box.offsetWidth * scaleFactor / 2) - window.innerWidth / 2;

  const scrollTopIncrement = (scrollTopEnd - initialScrollTop) / totalUpdates;
  const scrollLeftIncrement = (scrollLeftEnd - initialScrollLeft) / totalUpdates;

  let i = 0;
  const intervalId = setInterval(() => {
    rootEl.style.transform = `scale(${initialScale + scaleIncrement * i})`;
    htmlEl.scrollTop = initialScrollTop + scrollTopIncrement * i;
    htmlEl.scrollLeft = initialScrollLeft + scrollLeftIncrement * i;
    i++;
    if (i >= totalUpdates) {
      clearInterval(intervalId);
    }
    //   // Ensure final values are set correctly
    //   rootEl.style.transform = `scale(${scaleFactor})`;
    //   htmlEl.scrollTop = predictedBoxTop + box.offsetHeight * scaleFactor / 2 - window.innerHeight / 2;
    //   htmlEl.scrollLeft = predictedBoxLeft + box.offsetWidth * scaleFactor / 2 - window.innerWidth / 2;
    // }
  }, updateEveryNMs);
}

export default zoomAndScroll;
