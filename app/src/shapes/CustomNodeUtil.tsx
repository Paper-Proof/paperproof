import { GeoShapeUtil, Group2d, TLDefaultSizeStyle, TLGeoShape } from '@tldraw/tldraw';
import { SVGContainer } from '@tldraw/editor';
import React from 'react';

const STROKE_SIZES: Record<TLDefaultSizeStyle, number> = {
  s: 2,
  m: 3.5,
  l: 5,
  xl: 10,
}

export default class CustomNodeUtil extends GeoShapeUtil {
  static override type = 'customNode' as const

  override component(shape: TLGeoShape) {
    // Important to store it here and not later
    const superRender = super.component(shape);

    return <div
      className={shape.meta.isFocused ? "" : "node-not-focused"}
    >
      {superRender}
    </div>
  }
}
