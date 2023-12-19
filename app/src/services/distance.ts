const distance = (where: 'left'|'top', el1: HTMLElement, el2: HTMLElement) => {
  const rect1 = el1.getBoundingClientRect();
  const rect2 = el2.getBoundingClientRect();
  return Math.abs(rect1[where] - rect2[where]);
}

export default distance;
