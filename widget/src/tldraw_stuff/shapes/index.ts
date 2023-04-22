import type { CustomShapeUtil } from "./CustomShapeUtil";
import { NodeShape, NodeUtil } from "./node";

export type Shape = NodeShape;

export const shapeUtils = {
  node: new NodeUtil(),
};

export const getShapeUtils = <T extends Shape>(shape: T | T["type"]) => {
  if (typeof shape === "string")
    return shapeUtils[shape] as unknown as CustomShapeUtil<T>;
  return shapeUtils[shape.type] as unknown as CustomShapeUtil<T>;
};
