
// This is laggy 
useEffect(() => {
  const handleScroll = () => {
    const boxEl = document.getElementById('box-1')!;
    const elBottom = boxEl.getBoundingClientRect().bottom;
    console.log({ scrollTop: htmlEl.scrollTop, elBottom });
    if (elBottom < 0) {
      boxEl.clientHeight
      htmlEl.scrollTop = boxEl.offsetTop + boxEl.offsetHeight - 20;
      console.log("STOPPED scrolling");
    } else {
      console.log("Scrolled");
    }
  };
  window.addEventListener("scroll", handleScroll);
  return () => {
    window.removeEventListener("scroll", handleScroll);
  };
}, []);

function isElementInViewport (el) {
  var rect = el.getBoundingClientRect();
  const buffer = 0; // buffer of 50px

  return (
      rect.top + buffer >= 0 &&
      rect.left + buffer >= 0 &&
      rect.bottom - buffer <= (window.innerHeight || document.documentElement.clientHeight) &&
      rect.right - buffer <= (window.innerWidth || document.documentElement.clientWidth)
  );
}


// We can also do IntersectionObserver, that will be approximately the same result UX-wise

// Making {padding: 500px} static (not-scaled) is another option, which would have an additional benefit of scrollbars being meaningful.

