import { Editor, Box2d, TLAnimationOptions, TLShape, clamp } from "@tldraw/tldraw";

// This is a copypaste from Tldraw's `.zoomToBounds()`, except it allows to control `inset`
const zoomToBoundsWithInset = (editor: Editor, bounds: Box2d, inset: number, targetZoom?: number, animation?: TLAnimationOptions) => {
  if (!editor.instanceState.canMoveCamera) return editor;

  const { viewportScreenBounds } = editor;

  const MIN_ZOOM = 0.1
  const MAX_ZOOM = 8
  let zoom = clamp(
    Math.min(
      (viewportScreenBounds.width - inset) / bounds.width,
      (viewportScreenBounds.height - inset) / bounds.height
    ),
    MIN_ZOOM,
    MAX_ZOOM
  )

  if (targetZoom !== undefined) {
    zoom = Math.min(targetZoom, zoom)
  }

  editor.setCamera(
    {
      x: -bounds.minX + (viewportScreenBounds.width - bounds.width * zoom) / 2 / zoom,
      y: -bounds.minY + (viewportScreenBounds.height - bounds.height * zoom) / 2 / zoom,
      z: zoom,
    },
    animation
  )

  return editor
}

const zoomToWindow = (editor : Editor, window : TLShape) => {
  const bounds = editor.getShapePageBounds(window)!
  zoomToBoundsWithInset(editor, bounds, 20, 0.6, { duration: 200 });
}

export default zoomToWindow;
