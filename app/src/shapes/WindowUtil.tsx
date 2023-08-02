import React from 'react';
import { BaseBoxShapeUtil, SVGContainer, TLBaseShape, TLOnDoubleClickHandler } from '@tldraw/tldraw';
import zoomToWindow from '../services/zoomToWindow';

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

// Conceptually it's similar to tldraw's `FrameShapeUtil`.
// lakesare: I deleted all "reparentShapesById" methods for now. We can return them if we like, I just don't see much use in them currently.
export default class WindowUtil extends BaseBoxShapeUtil<WindowShapeType> {
  static override type = 'window'

  override canResize = () => false
  override hideSelectionBoundsFg = () => true

  override onDoubleClick: TLOnDoubleClickHandler<WindowShapeType> = (shape) => {
    zoomToWindow(this.editor, shape);

    // This is a fake "shape update" that updates nothing actually, we need this to avoid the creation of the new node (default tldraw behaviour if no shape updates happened on double click)
    return { id: shape.id, type: "window" };
  }

  override getDefaultProps(): WindowShapeType['props'] {
    return { w: 160 * 2, h: 90 * 2, name: "none", depth: 0, goalUsername: null, goalUsernameHeight: 20 };
  }

  override component(shape: WindowShapeType) {
    const bounds = this.editor.getPageBounds(shape)!

    return (
      <>
        <SVGContainer style={{
          pointerEvents: 'visible',
        }}>
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
            className={`window tl-frame_body depth-${shape.props.depth}`}
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
    // return <rect
    //   className="window-indicator"
    //   width={shape.props.w}
    //   height={shape.props.h}
    //   rx={5}
    //   ry={5}
    // />;
    return null
  }
}
