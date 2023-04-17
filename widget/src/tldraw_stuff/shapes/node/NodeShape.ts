import { TLShape } from '@tldraw/core'

export interface Definition {
  name: string
  type: string
}

/** */
export interface ProofTree {
  name: string
  toType: string
  fromType: string
  action: string
  children: (ProofTree | Definition)[]
}

export interface NodeShape extends TLShape {
  type: 'node'
  vars: string[]
  proofTree?: ProofTree
  name: string
}

export interface FrameShape extends TLShape {
  type: 'frame'
  proofTree: ProofTree
}
