import scrollIntoView from 'smooth-scroll-into-view-if-needed';

const zoomAndScroll = (event: React.MouseEvent<HTMLElement>) => {
  event.stopPropagation();
  const box = event.currentTarget.closest('.box') as HTMLElement;
  if (!box) return
  // 1. apply `transform: scale(scaleFactor)` so that `box` can fit into viewport
  const scaleFactor = Math.min(
    window.innerWidth / box.offsetWidth,
    window.innerHeight / box.offsetHeight
  );
  const rootEl = document.getElementById("root")!;
  rootEl.style.transform = `scale(${scaleFactor})`;

  // 2. scroll it into view
  // Predict where the `box` will be after the scale
  const boxRect = box.getBoundingClientRect();
  console.log(boxRect);
  const predictedBoxTop = box.offsetTop * scaleFactor;
  const predictedBoxLeft = box.offsetLeft * scaleFactor;

  // Apply the `scrollTop` and `.scrollLeft`
  // window.scroll({ top: predictedBoxTop, left: predictedBoxLeft })
  // window.scrollTo({ top: 50, left: 20 })
  // const bodyEl = document.getElementsByTagName("body")[0]
  // bodyEl.scroll(100, 50)

  scrollIntoView(box, {
    scrollMode: "always",
    block: "center",
    inline: "center"
  });

  // Make both the `scale() css transform` and
}

export default zoomAndScroll;
