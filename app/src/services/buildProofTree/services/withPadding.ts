import { Element } from "../../../types";

const withPadding = (padding: { left: number, right: number, top: number, bottom: number }, el: Element): Element => {
  return {
    size: [el.size[0] + padding.left + padding.right, el.size[1] + padding.top + padding.bottom],
    draw: (x, y) => {
      el.draw(x + padding.left, y + padding.top);
    }
  }
}

export default withPadding;
