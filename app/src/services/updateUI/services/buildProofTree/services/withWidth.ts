import { UIElement } from "types";

const withWidth = (width: number, el: UIElement): UIElement => {
  return {
    ...el,
    draw: (x, y) => {
      el.draw(x, y, width);
    }
  }
}

export default withWidth;
