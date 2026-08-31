const FLASH_CLASS = '-just-jumped-to';
const FLASH_MS = 2000;

// Pulses a ring around an element (see `.-just-jumped-to` in index.css)
const flashElement = (el: Element) => {
  el.classList.remove(FLASH_CLASS);
  // Forcing a reflow is what lets the animation restart when it's already running
  void (el as HTMLElement).offsetWidth;
  el.classList.add(FLASH_CLASS);
  setTimeout(() => el.classList.remove(FLASH_CLASS), FLASH_MS);
};

export default flashElement;
