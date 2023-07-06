import { Element } from '../../types';

export default function vStack(margin: number, boxes: Element[]): Element {
  if (boxes.length == 0) return { size: [0, 0], draw: () => { } };
  return {
    size: [
      Math.max(...boxes.map((b) => b.size[0])),
      boxes.map((b) => b.size[1]).reduce((x, y) => x + y) + (boxes.length - 1) * margin,
    ],
    draw(x, y, prefferedWidth) {
      let dy = 0;
      for (const box of boxes) {
        box.draw(x, y + dy, prefferedWidth);
        dy += box.size[1] + margin;
      }
    },
  };
}
