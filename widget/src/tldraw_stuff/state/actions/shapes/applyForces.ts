import { TLBoundsCorner, TLPointerInfo } from '@tldraw/core'
import { Body } from 'matter-js'
import { shapeUtils } from 'shapes'
import { Action } from 'state/constants'
import { mutables } from 'state/mutables'

export const applyForces: Action = (data, payload: { bodies: Body[] }) => {
  /* console.log(
    'Apply forces',
    payload.bodies.map(b => b.label)
  );*/
  const selectedIds = data.pageState.selectedIds
  //console.log('selectedIds', [...selectedIds], payload.bodies.length)
  for (const body of payload.bodies.slice()) {
    if (
      /*!selectedIds.includes(body.label) &&*/ Object.keys(data.page.shapes).includes(body.label)
    ) {
      const bds = body.bounds
      // console.log('body', body.label, body.position.y);
      data.page.shapes[body.label].point[0] = bds.min.x
      data.page.shapes[body.label].point[1] = bds.min.y
    }
  }
  /*data.page.shapes[shape.id] = shape
  data.pageState.selectedIds = [shape.id]

  mutables.pointedBoundsHandleId = TLBoundsCorner.BottomRight*/
}
