import type { TLPointerInfo } from '@tldraw/core'
import type { Action } from 'state/constants'
import { mutables } from 'state/mutables'

export const selectShape: Action = (data, payload: TLPointerInfo) => {
  const { selectedIds } = data.pageState

  if (payload.shiftKey) {
    if (selectedIds.includes(payload.target) && mutables.pointedShapeId !== payload.target) {
      selectedIds.splice(selectedIds.indexOf(payload.target), 1)
    } else {
      mutables.pointedShapeId = payload.target
      selectedIds.push(payload.target)
    }
  } else {
    const newId = Math.max(...Object.values(data.page.shapes).map((s) => s.childIndex)) + 1
    data.page.shapes[payload.target].childIndex = newId
    data.pageState.selectedIds = [payload.target]
  }
}
