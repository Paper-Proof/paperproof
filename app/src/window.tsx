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
    return { opacity: "1", w: 160 * 2, h: 90 * 2, name: "none" };
  }

  override render(shape: WindowShape) {
    const bounds = this.bounds(shape);

    function hash(text: string) {
      let hash = 0;
      if (text.length === 0) return hash;
      for (let i = 0; i < text.length; i++) {
        const chr = text.charCodeAt(i);
        hash = (hash << 5) - hash + chr;
        hash |= 0; // Convert to 32bit integer
      }
      return hash;
    }

    function getColor(text: string) {
      const x = hash(text + "ac");
      const h = Math.abs(x * 107) % 360;
      const s = 58 + (x % 18);
      const l = 90 + (h % 5);
      return `hsla(${h}, ${s}%, ${l}%, 1)`;
    }

    return (
      <>
        <SVGContainer>
          <rect
            className="tl-hitarea-stroke"
            width={bounds.width}
            height={bounds.height}
          />
          <rect
            className="tl-frame_body"
            width={bounds.width}
            height={bounds.height}
            fill={getColor(shape.props.name)}
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
