import Vec from '@tldraw/vec'
import { shapeUtils } from 'shapes'
import { Action } from 'state/constants'

export const splitGhostShapes: Action = (data) => {
  const toSplit = Object.values(data.page.shapes).filter((shape) => shape.isGhost)
  const idsToDelete = toSplit.map((shape) => shape.id)

  for (const shape of toSplit) {
    if (shape.type === 'node' && shape.vars.length > 1) {
      if (!shape.vars[0].startsWith('∀')) {
        const offsets = [-200, 200]
        const vars = [[shape.vars[0]], shape.vars.splice(1)]
        for (const id of [0, 1]) {
          const newShape = shapeUtils.node.getShape({
            parentId: 'page1',
            point: Vec.add(shape.point, [offsets[id], 0]),
            vars: vars[id],
            childIndex: Object.values(data.page.shapes).length,
          })
          data.page.shapes[newShape.id] = newShape
        }
      }
    }
    data.overlays.eraseLine = []
    delete data.page.shapes[shape.id]
  }

  data.pageState.selectedIds = data.pageState.selectedIds.filter((id) => !idsToDelete.includes(id))

  if (data.pageState.hoveredId && idsToDelete.includes(data.pageState.hoveredId)) {
    data.pageState.hoveredId = undefined
  }
}
