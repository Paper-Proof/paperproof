import { Element } from '../../types';

// hStack aligns to the bottom
export default function hStack(margin: number, ...boxes: Element[]): Element {
  if (boxes.length == 0) return { size: [0, 0], draw: () => { } };
  const [w, h] = [
    boxes.map((b) => b.size[0]).reduce((x, y) => x + y) + (boxes.length - 1) * margin,
    Math.max(...boxes.map((b) => b.size[1])),
  ];
  return {
    size: [w, h],
    draw(x, y) {
      let dx = 0;
      for (const box of boxes) {
        box.draw(x + dx, y + h - box.size[1]);
        dx += box.size[0] + margin;
      }
    },
  };
}