import { UIElement } from 'types';

const vStack = (margin: number, boxes: UIElement[]): UIElement => {
  if (boxes.length == 0) return { size: [0, 0], draw: () => { } };
  const maxWidth = Math.max(...boxes.map((b) => b.size[0]));
  return {
    size: [
      maxWidth,
      boxes.map((b) => b.size[1]).reduce((x, y) => x + y) + (boxes.length - 1) * margin,
    ],
    draw(x, y, preferredWidth) {
      let dy = 0;
      for (const box of boxes) {
        box.draw(x, y + dy, preferredWidth);
        dy += box.size[1] + margin;
      }
    },
  };
}

export default vStack;
