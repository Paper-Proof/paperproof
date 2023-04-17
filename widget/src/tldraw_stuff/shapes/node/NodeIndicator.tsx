import { TLShapeUtil } from '@tldraw/core'
import * as React from 'react'
import { getRects } from './NodeComponent'
import { NodeShape } from './NodeShape'

export const NodeIndicator = TLShapeUtil.Indicator<NodeShape>(({ shape }) => {
  const [size] = shape.vars.length > 0 ? getRects([...shape.vars].reverse()) : [[800, 500]]
  return (
    <rect
      x={-5}
      y={-5}
      pointerEvents="none"
      width={size[0] + 10}
      height={size[1] + 10}
      fill="none"
      stroke="tl-selectedStroke"
      strokeWidth={3}
    />
  )
})
