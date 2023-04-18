import type { TLPointerInfo } from '@tldraw/core'
import Vec from '@tldraw/vec'
import { getShapeUtils } from 'shapes'
import type { Action } from 'state/constants'
import { mutables } from 'state/mutables'

export const updateEraseLine: Action = (data, payload: TLPointerInfo) => {
  const { currentPoint } = mutables
  const { eraseLine } = data.overlays
  const p = currentPoint
  data.overlays.eraseLine = [...eraseLine, p]
}
