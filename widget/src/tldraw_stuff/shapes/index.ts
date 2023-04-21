import type { CustomShapeUtil } from "./CustomShapeUtil";
import { BoxShape, BoxUtil } from "./box";
import { NodeShape, NodeUtil } from "./node";
import { PencilShape, PencilUtil } from "./pencil";

export * from "./pencil";
export * from "./box";

export type Shape = BoxShape | PencilShape | NodeShape;

export const shapeUtils = {
  node: new NodeUtil(),
  box: new BoxUtil(),
  pencil: new PencilUtil(),
};

export const getShapeUtils = <T extends Shape>(shape: T | T["type"]) => {
  if (typeof shape === "string")
    return shapeUtils[shape] as unknown as CustomShapeUtil<T>;
  return shapeUtils[shape.type] as unknown as CustomShapeUtil<T>;
};
