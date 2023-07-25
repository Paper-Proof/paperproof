import React from 'react';
import { BaseBoxShapeUtil, HTMLContainer, SVGContainer, TLBaseShape, TLGroupShape, TLOnResizeEndHandler, TLShape, TLShapeId } from '@tldraw/tldraw'

export type WindowShapeType = TLBaseShape<'window',
  {
    name: string;
    w: number;
    h: number;
    depth: number;
    goalUsername: string | null,
    goalUsernameHeight: number
  }
>

// Most of the methods are copypasted from tldraw's `FrameShapeUtil`
export default class WindowUtil extends BaseBoxShapeUtil<WindowShapeType> {
  static override type = 'window'

  override getDefaultProps(): WindowShapeType['props'] {
    return { w: 160 * 2, h: 90 * 2, name: "none", depth: 0, goalUsername: null, goalUsernameHeight: 20 };
  }

  override component(shape: WindowShapeType) {
    const bounds = this.editor.getBounds(shape);

    return (
      <>
        <SVGContainer>
          <rect
            className="tl-hitarea-stroke"
            width={bounds.width}
            height={bounds.height}
            rx={5}
            ry={5}
            // Removes a weird tiny grey border around all windows
            // (https://stackoverflow.com/a/64236704/3192470)
            shapeRendering="crispEdges"
            // Makes it possible to use rgba-s with alpha channels
            // (https://stackoverflow.com/a/11293812/3192470)
            fill="white"
          />
          <rect
            className={`tl-frame_body depth-${shape.props.depth}`}
            width={bounds.width}
            height={bounds.height}
            rx={5}
            ry={5}
            shapeRendering="crispEdges"
          />
        </SVGContainer>
        {
          shape["props"].goalUsername &&
          <div style={{ height: shape["props"].goalUsernameHeight }} className="goalUsername">
            {shape["props"].goalUsername}
          </div>
        }
      </>
    );
  }

  override indicator(shape: WindowShapeType) {
    return <rect width={shape.props.w} height={shape.props.h} />;
  }


  override canReceiveNewChildrenOfType = (shape: TLShape, _type: TLShape['type']) => {
    return !shape.isLocked
  }

  // override providesBackgroundForChildren(): boolean {
  //   return true
  // }

  override canDropShapes = (shape: WindowShapeType, _shapes: TLShape[]): boolean => {
    return !shape.isLocked
  }

  override onDragShapesOver = (frame: WindowShapeType, shapes: TLShape[]): { shouldHint: boolean } => {
    if (!shapes.every((child) => child.parentId === frame.id)) {
      this.editor.reparentShapesById(
        shapes.map((shape) => shape.id),
        frame.id
      )
      return { shouldHint: true }
    }
    return { shouldHint: false }
  }

  override onDragShapesOut = (_shape: WindowShapeType, shapes: TLShape[]): void => {
    const parent = this.editor.getShapeById(_shape.parentId)
    const isInGroup = parent && this.editor.isShapeOfType<TLGroupShape>(parent, 'group')

    // If frame is in a group, keep the shape
    // moved out in that group
    if (isInGroup) {
      this.editor.reparentShapesById(
        shapes.map((shape) => shape.id),
        parent.id
      )
    } else {
      this.editor.reparentShapesById(
        shapes.map((shape) => shape.id),
        this.editor.currentPageId
      )
    }
  }

  override onResizeEnd: TLOnResizeEndHandler<WindowShapeType> = (shape) => {
    const bounds = this.editor.getPageBounds(shape)!
    const children = this.editor.getSortedChildIds(shape.id)

    const shapesToReparent: TLShapeId[] = []

    for (const childId of children) {
      const childBounds = this.editor.getPageBoundsById(childId)!
      if (!bounds.includes(childBounds)) {
        shapesToReparent.push(childId)
      }
    }

    if (shapesToReparent.length > 0) {
      this.editor.reparentShapesById(shapesToReparent, this.editor.currentPageId)
    }
  }
}
