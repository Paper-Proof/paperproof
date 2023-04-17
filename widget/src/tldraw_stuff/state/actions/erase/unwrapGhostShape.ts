import Vec from '@tldraw/vec'
import { getShapeUtils, shapeUtils } from 'shapes'
import { Action } from 'state/constants'
import { mutables } from 'state/mutables'

export const unwrapGhostShape: Action = (data) => {
  const toSplit = Object.values(data.page.shapes).filter((shape) => shape.isGhost)
  const idsToDelete = toSplit.map((shape) => shape.id)
  const { snapshot, currentPoint, initialPoint } = mutables

  const delta = Vec.sub(currentPoint, initialPoint)

  data.pageState.selectedIds.forEach((id) => {
    const initialShape = snapshot.page.shapes[id]
    const movedShape = data.page.shapes[id]
    movedShape.point = Vec.add(initialShape.point, delta)

    const utils = getShapeUtils('node')

    Object.values(data.page.shapes)
      .filter((shape) => shape != movedShape)
      .filter((shape) => utils.hitTestBounds(shape, utils.getBounds(movedShape)))
      .forEach((shape) => {
        if (shape.type === 'node' && shape.vars.length > 1) {
          if (shape.vars[0].startsWith('∀')) {
            const newShape = shapeUtils.node.getShape({
              parentId: 'page1',
              point: shape.point,
              vars: shape.vars.splice(1),
              childIndex: Object.values(data.page.shapes).length,
            })
            data.page.shapes[newShape.id] = newShape

            const idsToDelete = [id, shape.id]
            for (const id of idsToDelete) {
              delete data.page.shapes[id]
            }
            data.pageState.selectedIds = data.pageState.selectedIds.filter(
              (id) => !idsToDelete.includes(id)
            )

            if (data.pageState.hoveredId && idsToDelete.includes(data.pageState.hoveredId)) {
              data.pageState.hoveredId = undefined
            }

            console.log('dbg found hit', shape)
          }
        }
      })

    /*Object.values(data.page.shapes)
    .filter((shape) => !shape.isGhost && shape != movedShape)
    .filter(shape => utils.hitTestBounds(shape, utils.getBounds(movedShape))).forEach(shape => {
  
      data.pageState.selectedIds = data.pageState.selectedIds.filter(id => !idsToDelete.includes(id))
  
      if (data.pageState.hoveredId && idsToDelete.includes(data.pageState.hoveredId)) {
        data.pageState.hoveredId = undefined
      }
    }*/
  })
}
