import { GeoShapeUtil, TLGeoShape } from '@tldraw/tldraw';
import React from 'react';

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
