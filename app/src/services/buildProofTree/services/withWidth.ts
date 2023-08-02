import { Element } from "../../../types";

const withWidth = (width: number, el: Element): Element => {
  return {
    ...el,
    draw: (x, y) => {
      el.draw(x, y, width);
    }
  }
}

export default withWidth;
