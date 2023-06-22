import React from "react";
import {
  OnResizeEndHandler,
  SVGContainer,
  TLBaseShape,
  TLBoxUtil,
  TLOpacityType,
  defineShape,
} from "@tldraw/tldraw";
import { TLShape, TLShapeId } from "@tldraw/tlschema";

/*const colors = [
  "#eceff1",
  "#cfd8dc",
  "#b0bec5"
]*/

// Cool grey material dark palette
const colors = [
  "#1f2933",
  "#323f4b",
  "#3e4c59",
  "#52606d",
  "#616e7c",
  "#7b8794",
  "#9aa5b1",
  "#cbd2d9",
  "#e4e7eb",
  "#f5f7fa"
].reverse()

// Shape Type
// ----------
// Every shape needs an opacity prop (for now), but other than that
// you can add whatever you want, so long as it's JSON serializable.
type WindowShape = TLBaseShape<
  "window",
  {
    name: string;
    w: number;
    h: number;
    depth: number;
    opacity: TLOpacityType;
  }
>;

// Shape Definition
// ----------------
// The shape definition is used to tell TypeScript about the shape
// and to register the shape with the app.
export const WindowShape = defineShape<WindowShape>({
  type: "window",
  getShapeUtil: () => WindowUtil,
  // validator: createShapeValidator({ ... })
});

/** @public */
export class WindowUtil extends TLBoxUtil<WindowShape> {
  static type = "window";

  override canBind = () => true;

  override canEdit = () => true;

  override defaultProps(): WindowShape["props"] {
    return { opacity: "1", w: 160 * 2, h: 90 * 2, name: "none", depth: 0 };
  }

  override render(shape: WindowShape) {
    const bounds = this.bounds(shape);

    return (
      <>
        <SVGContainer>
          <rect
            className="tl-hitarea-stroke"
            width={bounds.width}
            height={bounds.height}
            rx={5}
            ry={5}
          />
          <rect
            className="tl-frame_body"
            width={bounds.width}
            height={bounds.height}
            fill={colors[shape.props.depth]}
            rx={5}
            ry={5}
            filter="drop-shadow(3px 5px 2px rgb(0 0 0 / 0.4))"
          />
        </SVGContainer>
      </>
    );
  }

  override canReceiveNewChildrenOfType = (_type: TLShape["type"]) => {
    return true;
  };

  override canDropShapes = (
    _shape: WindowShape,
    _shapes: TLShape[]
  ): boolean => {
    return true;
  };

  override onDragShapesOver = (
    frame: WindowShape,
    shapes: TLShape[]
  ): { shouldHint: boolean } => {
    if (!shapes.every((child) => child.parentId === frame.id)) {
      this.app.reparentShapesById(
        shapes.map((shape) => shape.id),
        frame.id
      );
      return { shouldHint: true };
    }
    return { shouldHint: false };
  };

  onDragShapesOut = (_shape: WindowShape, shapes: TLShape[]): void => {
    const parentId = this.app.getShapeById(_shape.parentId);
    const isInGroup = parentId?.type === "group";

    // If frame is in a group, keep the shape
    // moved out in that group
    if (isInGroup) {
      this.app.reparentShapesById(
        shapes.map((shape) => shape.id),
        parentId.id
      );
    } else {
      this.app.reparentShapesById(
        shapes.map((shape) => shape.id),
        this.app.currentPageId
      );
    }
  };

  override onResizeEnd: OnResizeEndHandler<WindowShape> = (shape) => {
    const bounds = this.app.getPageBounds(shape)!;
    const children = this.app.getSortedChildIds(shape.id);

    const shapesToReparent: TLShapeId[] = [];

    for (const childId of children) {
      const childBounds = this.app.getPageBoundsById(childId)!;
      if (!bounds.includes(childBounds)) {
        shapesToReparent.push(childId);
      }
    }

    if (shapesToReparent.length > 0) {
      this.app.reparentShapesById(shapesToReparent, this.app.currentPageId);
    }
  };

  // The indicator is used when hovering over a shape or when it's selected.
  // This can only be SVG path data; generally you want the outline of the
  // component you're rendering.
  indicator(shape: WindowShape) {
    return <rect width={shape.props.w} height={shape.props.h} />;
  }
}
