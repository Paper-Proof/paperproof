import { TLBounds, Utils } from '@tldraw/core'
import { intersectLineSegmentBounds } from '@tldraw/intersect'
import { nanoid } from 'nanoid'
import { CustomShapeUtil } from 'shapes/CustomShapeUtil'
import { NodeComponent, getRects } from './NodeComponent'
import { NodeIndicator } from './NodeIndicator'
import { NodeShape } from './NodeShape'

type T = NodeShape
type E = SVGSVGElement

export class NodeUtil extends CustomShapeUtil<T, E> {
  Component = NodeComponent

  Indicator = NodeIndicator

  hideResizeHandles = true
  hideBounds = true

  getBounds = (shape: T) => {
    const bounds = Utils.getFromCache(this.boundsCache, shape, () => {
      if (shape.vars.length == 0) {
        const [minX, minY, width, height] = [0, 0, 800, 500]
        return { minX, maxX: minX + width, minY, maxY: minY + height, width, height }
      }
      const [[width, height]] = getRects([...shape.vars].reverse())

      return {
        minX: 0,
        maxX: width,
        minY: 0,
        maxY: height,
        width,
        height,
      } as TLBounds
    })

    return Utils.translateBounds(bounds, shape.point)
  }

  /* ----------------- Custom Methods ----------------- */

  canBind = true

  getShape = (props: Partial<T>): T => {
    return {
      id: nanoid(),
      type: 'node',
      name: 'Node',
      parentId: 'page1',
      point: [0, 0],
      childIndex: 1,
      vars: [],
      ...props,
    }
  }

  shouldRender = (prev: T, next: T) => {
    return false
  }

  getCenter = (shape: T) => {
    return Utils.getBoundsCenter(this.getBounds(shape))
  }

  hitTestPoint = (shape: T, point: number[]) => {
    return Utils.pointInBounds(point, this.getBounds(shape))
  }

  hitTestLineSegment = (shape: T, A: number[], B: number[]) => {
    return intersectLineSegmentBounds(A, B, this.getBounds(shape)).length > 0
  }

  transform = (shape: T, bounds: TLBounds, initialShape: T, scale: number[]) => {
    shape.point = [bounds.minX, bounds.minY]
  }
}
