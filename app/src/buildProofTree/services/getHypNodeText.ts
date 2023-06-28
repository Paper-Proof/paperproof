import { HypNode } from "../../types";

export default function getHypNodeText(node: HypNode) {
  const text = (() => {
    if (!node.name) {
      return node.text;
    }
    // For cases h._@.Examples._hyg.1162
    const hypName = node.name.includes(".")
      ? `${node.name.split(".")[0]}✝`
      : node.name;
    return `${hypName}: ${node.text}`;
  })();
  const devId = localStorage.getItem("dev") === 'true'
    ? ' ' + node.id
    : '';
  return `${text}${devId}`;
}
