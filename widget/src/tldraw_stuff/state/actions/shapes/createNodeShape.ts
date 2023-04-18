import { TLBoundsCorner, TLPointerInfo } from '@tldraw/core'
import { shapeUtils } from 'shapes'
import { ProofTree } from 'shapes/node'
import { Action } from 'state/constants'
import { mutables } from 'state/mutables'

function randInt(n: number) {
  return Math.floor(Math.random() * n)
}

function choose(choices: string[]) {
  return choices[randInt(choices.length)]
}

export const createNodeShape: Action = (
  data,
  payload: { pos?: number[]; name?: string; type?: string[]; proofTree?: ProofTree }
) => {
  function createShape() {
    if (payload.proofTree) {
      console.log('pp', payload.proofTree)
      return shapeUtils.node.getShape({
        parentId: 'page1',
        point: payload.pos ?? mutables.currentPoint,
        proofTree: payload.proofTree,
        vars: [],
        name: payload.name ?? 'noname',
        childIndex: Object.values(data.page.shapes).length,
      })
    } else {
      let vars: string[] = []
      if (!payload.name || !payload.type) {
        const num = 2 + randInt(2)
        for (let i = 0; i < num; i++) {
          vars.push(choose(['p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z']))
        }
      } else if (payload.type) {
        vars = [...payload.type]
      }
      return shapeUtils.node.getShape({
        parentId: 'page1',
        point: payload.pos ?? mutables.currentPoint,
        vars,
        name: payload.name ?? 'noname',
        childIndex: Object.values(data.page.shapes).length,
      })
    }
  }
  const shape = createShape()

  data.page.shapes[shape.id] = shape
  data.pageState.selectedIds = [shape.id]

  mutables.pointedBoundsHandleId = TLBoundsCorner.BottomRight
}
