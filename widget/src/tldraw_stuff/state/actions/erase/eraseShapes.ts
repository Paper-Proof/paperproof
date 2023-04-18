import type { TLPointerInfo } from '@tldraw/core'
import { getShapeUtils } from 'shapes'
import type { Action } from 'state/constants'
import { mutables } from 'state/mutables'

export const eraseShapes: Action = (data, payload: TLPointerInfo) => {
  const line = data.overlays.eraseLine
  if (line.length < 2) {
    return
  }
  const [previousPoint, currentPoint] = line.slice(-2)

  Object.values(data.page.shapes)
    .filter((shape) => !shape.isGhost)
    .forEach((shape) => {
      if (getShapeUtils(shape).hitTestLineSegment(shape, previousPoint, currentPoint)) {
        shape.isGhost = true
      }
    })
}
