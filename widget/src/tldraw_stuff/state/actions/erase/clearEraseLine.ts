import type { TLPointerInfo } from '@tldraw/core'
import Vec from '@tldraw/vec'
import { getShapeUtils } from 'shapes'
import type { Action } from 'state/constants'
import { mutables } from 'state/mutables'

export const clearEraseLine: Action = (data, payload: TLPointerInfo) => {
  data.overlays.eraseLine = []
}
