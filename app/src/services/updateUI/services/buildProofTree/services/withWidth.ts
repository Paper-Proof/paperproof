import { UIElement } from "types";

const withWidth = (width: number | (() => number), el: UIElement): UIElement => {
  return {
    ...el,
    draw: (x, y) => {
      el.draw(x, y, (width instanceof Function) ? width() : width);
    }
  }
}

export default withWidth;
