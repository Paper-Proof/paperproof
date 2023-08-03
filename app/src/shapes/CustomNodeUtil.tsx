import { GeoShapeUtil, TLGeoShape } from '@tldraw/tldraw';
import React from 'react';

export default class CustomNodeUtil extends GeoShapeUtil {
  static override type = 'customNode' as const

  override canResize = () => false
  override canEdit = () => false
  override hideSelectionBoundsFg = () => true
  override hideSelectionBoundsBg = () => true
  override hideRotateHandle = () => true
  override hideResizeHandles = () => true

  override canUnmount = () => false

  override component(shape: TLGeoShape) {
    // Important to store it here and not later
    const superRender = super.component(shape);

    return <div
      className={shape.meta.isFocused ? "" : "node-not-focused"}
    >
      {superRender}
    </div>
  }

  override indicator(shape: TLGeoShape) {
    // Can't return null here because of GeoShapeUtil's typings
    return <div/>
  }
}
