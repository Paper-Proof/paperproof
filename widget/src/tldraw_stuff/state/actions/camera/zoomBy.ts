import type { TLPointerInfo } from '@tldraw/core'
import Vec from '@tldraw/vec'
import type { Action } from 'state/constants'

function clamp(x: number) {
  return Math.min(Math.max(x, 0.1), 5)
}

export const zoomBy: Action = (data, payload: TLPointerInfo) => {
  const delta = payload.delta[2] / 50
  const center = payload.point
  const { zoom, point } = data.pageState.camera
  const nextZoom = clamp(zoom - delta * zoom)
  const p0 = Vec.sub(Vec.div(center, zoom), point)
  const p1 = Vec.sub(Vec.div(center, nextZoom), point)
  const newPoint = Vec.toFixed(Vec.add(point, Vec.sub(p1, p0)))

  data.pageState.camera.zoom = nextZoom
  data.pageState.camera.point = newPoint
}
