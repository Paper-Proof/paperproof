import { useStateDesigner } from '@state-designer/react'

import {
  Renderer,
  TLBounds,
  TLKeyboardEventHandler,
  TLPinchEventHandler,
  TLPointerEventHandler,
  TLWheelEventHandler,
} from '@tldraw/core'
import axios from 'axios'
import {
  Bodies,
  Composite,
  Engine,
  Events,
  Mouse,
  MouseConstraint,
  Render,
  Runner,
  World,
} from 'matter-js'
import * as React from 'react'
import { ProofTree } from './shapes/node'
import { createNodeShape } from './state/actions'
import { Api } from './state/api'
import { mutables } from './state/mutables'
import styled from 'stitches.config'
import { TitleLinks } from './components/TitleLinks'
import { Toolbar } from './components/Toolbar'
import { getShapeUtils, shapeUtils } from './shapes'
import { machine } from './state/machine'



// TODO import this later
// import './styles.css'

const proofTree: ProofTree = {
  toType: '∃ p, p ≥ N ∧ Nat.Prime p',
  name: 'top level',
  fromType: '∀ (N : ℕ), ∃ p, p ≥ N ∧ Nat.Prime p',
  children: [
    {
      toType: '✅',
      name: '',
      fromType: '∃ p, p ≥ N ∧ Nat.Prime p',
      children: [
        { type: '', name: '✅' },
        { type: '$$$$', name: ' Exists.intro ' },
        { type: '', name: 'p := Nat.minFac  M ' },
        { type: '$$$$', name: ' And.intro ' },
        {
          toType: '¬p ≥ N → False',
          name: 'ppos',
          fromType: 'p ≥ N',
          children: [
            {
              toType: 'False',
              name: '',
              fromType: '¬p ≥ N → False',
              children: [
                {
                  toType: '✅',
                  name: '',
                  fromType: 'False',
                  children: [
                    { type: '', name: '✅' },
                    { type: '$$$$', name: 'Nat.Prime.not_dvd_one' },
                    {
                      toType: 'M ≠ 1',
                      name: 'pp',
                      fromType: 'Nat.Prime p',
                      children: [
                        {
                          toType: '✅',
                          name: '',
                          fromType: 'M ≠ 1',
                          children: [{ type: '', name: '✅' }],
                          action: ' linarith ',
                        },
                        { type: '$$$$', name: 'Nat.minFac_prime' },
                      ],
                      action: 'apply  Nat.minFac_prime ',
                    },
                    {
                      toType: '✅',
                      name: 'h',
                      fromType: 'p ∣ 1',
                      children: [
                        { type: '', name: '✅' },
                        { type: '$$$$', name: 'Nat.dvd_add_right' },
                        {
                          toType: 'p ≤ N',
                          name: 'h₁',
                          fromType: 'p ∣ Nat.factorial N',
                          children: [
                            {
                              toType: '✅',
                              name: '',
                              fromType: 'p ≤ N',
                              children: [
                                { type: '', name: '✅' },
                                { type: '$$$$', name: 'le_of_not_ge' },
                                { type: '¬p ≥ N', name: 'pln' },
                              ],
                              action: 'exact le_of_not_ge  pln ',
                            },
                            {
                              toType: 'M ≠ 1',
                              name: 'pp',
                              fromType: 'Nat.Prime p',
                              children: [
                                {
                                  toType: '✅',
                                  name: '',
                                  fromType: 'M ≠ 1',
                                  children: [{ type: '', name: '✅' }],
                                  action: ' linarith ',
                                },
                                { type: '$$$$', name: 'Nat.minFac_prime' },
                              ],
                              action: 'apply  Nat.minFac_prime ',
                            },
                            { type: '$$$$', name: 'dvd_factorial' },
                            { type: '$$$$', name: 'mpr' },
                            { type: '$$$$', name: '? _ ' },
                          ],
                          action: 'refine pp.dvd_factorial.mpr ? _ ',
                        },
                        { type: '$$$$', name: 'mp' },
                        {
                          toType: '✅',
                          name: 'h₂',
                          fromType: 'p ∣ Nat.factorial N + 1',
                          children: [
                            { type: '', name: '✅' },
                            { type: '$$$$', name: 'Nat.minFac_dvd' },
                            { type: '', name: 'M := Nat.factorial N +  1 ' },
                          ],
                          action: 'exact Nat.minFac_dvd M',
                        },
                      ],
                      action: 'exact Iff.mp (Nat.dvd_add_right h₁) h₂',
                    },
                  ],
                  action: 'exact Nat.Prime.not_dvd_one pp  h ',
                },
                { type: '¬p ≥ N', name: 'pln' },
              ],
              action: 'intro  pln ',
            },
            { type: '$$$$', name: 'by_contradiction' },
          ],
          action: 'apply  by_contradiction ',
        },
        {
          toType: 'M ≠ 1',
          name: 'pp',
          fromType: 'Nat.Prime p',
          children: [
            {
              toType: '✅',
              name: '',
              fromType: 'M ≠ 1',
              children: [{ type: '', name: '✅' }],
              action: ' linarith ',
            },
            { type: '$$$$', name: 'Nat.minFac_prime' },
          ],
          action: 'apply  Nat.minFac_prime ',
        },
      ],
      action: 'exact ⟨ p, ppos, pp  ⟩ ',
    },
    { type: 'ℕ', name: 'N' },
  ],
  action: 'intro  N ',
}

declare const window: Window & { api: Api }

const onHoverShape: TLPointerEventHandler = (info, e) => {
  machine.send('HOVERED_SHAPE', info)
}

const onUnhoverShape: TLPointerEventHandler = (info, e) => {
  machine.send('UNHOVERED_SHAPE', info)
}

const onPointShape: TLPointerEventHandler = (info, e) => {
  machine.send('POINTED_SHAPE', info)
}

const onPointCanvas: TLPointerEventHandler = (info, e) => {
  machine.send('POINTED_CANVAS', info)
}

const onPointBounds: TLPointerEventHandler = (info, e) => {
  machine.send('POINTED_BOUNDS', info)
}

const onPointHandle: TLPointerEventHandler = (info, e) => {
  machine.send('POINTED_HANDLE', info)
}

const onPointerDown: TLPointerEventHandler = (info, e) => {
  machine.send('STARTED_POINTING', info)
}

const onPointerUp: TLPointerEventHandler = (info, e) => {
  machine.send('STOPPED_POINTING', info)
}

const onPointerMove: TLPointerEventHandler = (info, e) => {
  machine.send('MOVED_POINTER', info)
}

const onPan: TLWheelEventHandler = (info, e) => {
  machine.send('PANNED', info)
}

const onPinchStart: TLPinchEventHandler = (info, e) => {
  machine.send('STARTED_PINCHING', info)
}

const onPinch: TLPinchEventHandler = (info, e) => {
  machine.send('PINCHED', info)
}

const onPinchEnd: TLPinchEventHandler = (info, e) => {
  machine.send('STOPPED_PINCHING', info)
}

const onZoom: TLWheelEventHandler = (info, e) => {
  machine.send('ZOOM_BY', info)
}

const onPointBoundsHandle: TLPinchEventHandler = (info, e) => {
  machine.send('POINTED_BOUNDS_HANDLE', info)
}

const onBoundsChange = (bounds: TLBounds) => {
  machine.send('RESIZED', { bounds })
}

const onKeyDown: TLKeyboardEventHandler = (key, info, e) => {
  switch (key) {
    case 'Alt':
    case 'Meta':
    case 'Control':
    case 'Shift': {
      machine.send('TOGGLED_MODIFIER', info)
      break
    }
    case 'Backspace': {
      machine.send('DELETED', info)
      break
    }
    case 'Escape': {
      machine.send('CANCELLED', info)
      break
    }
    case '0': {
      machine.send('ZOOMED_TO_ACTUAL', info)
      break
    }
    case '1': {
      machine.send('ZOOMED_TO_FIT', info)
      break
    }
    case '2': {
      machine.send('ZOOMED_TO_SELECTION', info)
      break
    }
    case '=': {
      if (info.metaKey || info.ctrlKey) {
        e.preventDefault()
        machine.send('ZOOMED_IN', info)
      }
      break
    }
    case '-': {
      if (info.metaKey || info.ctrlKey) {
        e.preventDefault()
        machine.send('ZOOMED_OUT', info)
      }
      break
    }
    case 's':
    case 'v': {
      machine.send('SELECTED_TOOL', { name: 'select' })
      break
    }
    case 'r':
    case 'b': {
      machine.send('SELECTED_TOOL', { name: 'box' })
      break
    }
    case 'd': {
      machine.send('SELECTED_TOOL', { name: 'pencil' })
      break
    }
    case 'e': {
      machine.send('SELECTED_TOOL', { name: 'eraser' })
      break
    }
    case 'a': {
      if (info.metaKey || info.ctrlKey) {
        machine.send('SELECTED_ALL')
        e.preventDefault()
      } else {
        machine.send('SELECTED_TOOL', { name: 'arrow' })
      }
      break
    }
    case 'z': {
      if (info.metaKey || info.ctrlKey) {
        if (info.shiftKey) {
          machine.send('REDO')
        } else {
          machine.send('UNDO')
        }
      }
      break
    }
  }
}

const onKeyUp: TLKeyboardEventHandler = (key, info, e) => {
  switch (key) {
    case 'Alt':
    case 'Meta':
    case 'Control':
    case 'Shift': {
      machine.send('TOGGLED_MODIFIER', info)
      break
    }
  }
}

interface AppProps {
  onMount?: (api: Api) => void
}

function toGoodFormat(s: { type: string; v: string }[]): string[] {
  // forall eps, forall eps > 0 - should go to -> forall eps > 0
  let currentType = 'dd'
  let buffer: string[] = []
  const res: string[] = []
  function flush() {
    if (buffer.length) {
      // If it starts with introduction, but follow with condition - remove it, e.g. forall eps : Nat
      if (buffer.length > 1 && buffer[0].match(/^\p{L}($| : )/u)) {
        buffer = buffer.slice(1)
      }
      res.push(currentType + buffer.join(' '))
    }
  }
  for (const { type, v } of s) {
    if (type == currentType) {
      buffer.push(v)
    } else {
      flush()
      buffer = [v]
      currentType = type
    }
  }
  flush()
  return res
}

let lastId = 0

export default function App({ onMount }: AppProps) {
  const appState = useStateDesigner(machine)

  React.useEffect(() => {
    const engine = Engine.create()
    engine.gravity = { x: 0, y: 0, scale: 1 }
    Runner.run(engine)

    const utils = getShapeUtils('node')
    const canvas = document.getElementsByClassName('tl-canvas')

    const render = Render.create({
      canvas: document.getElementById('mcanvas') as HTMLCanvasElement,
      engine,
      options: { wireframeBackground: 'transparent' },
    })
    function setRenderSize() {
      render.options.width = window.innerWidth
      render.options.height = window.innerHeight
      render.canvas.width = window.innerWidth
      render.canvas.height = window.innerHeight
    }
    setRenderSize()
    window.addEventListener('resize', setRenderSize)

    const FUNCTION_CATEGORY = 0b1
    const OBJECT_CATEGORY = 0b10
    const MOUSE_CATEGORY = 0b100

    Render.run(render)
    const mouse = Mouse.create(canvas[0] as HTMLElement)
    const constraint = MouseConstraint.create(engine, { mouse })
    constraint.collisionFilter.category = MOUSE_CATEGORY
    World.add(engine.world, constraint)
    Events.on(constraint, 'startdrag', (e) => {
      e.body.collisionFilter.mask = ~0 ^ FUNCTION_CATEGORY
    })
    Events.on(constraint, 'enddrag', (e) => {
      e.body.collisionFilter.mask = ~0
    })
    Events.on(engine, 'afterUpdate', () => {
      const { point, zoom } = appState.data.pageState.camera
      render.options.hasBounds = true
      render.bounds.min.x = -point[0]
      render.bounds.min.y = -point[1]
      render.bounds.max.x = render.bounds.min.x + window.innerWidth / zoom
      render.bounds.max.y = render.bounds.min.y + window.innerHeight / zoom
      constraint.mouse.offset = { x: -point[0], y: -point[1] }
      constraint.mouse.scale = { x: 1 / zoom, y: 1 / zoom }
      if (appState.data.overlays.eraseLine.length > 0) {
        constraint.collisionFilter.mask = 0
      } else {
        constraint.collisionFilter.mask = ~0
      }
    })

    const tick = () => {
      const shapes = Object.values(appState.data.page.shapes)
      for (const shape of shapes) {
        if (shape.type !== 'node') {
          continue
        }
        for (const body of engine.world.bodies) {
          if (!shapes.some((s) => s.id == body.label)) {
            World.remove(engine.world, body)
          }
        }
        if (!engine.world.bodies.some((b) => b.label == shape.id)) {
          const bds = utils.getBounds(shape)
          const category =
            shape.vars.length > 0 && shape.vars[0].startsWith('∀')
              ? FUNCTION_CATEGORY
              : OBJECT_CATEGORY
          const box = Bodies.rectangle(
            bds.minX + bds.width / 2,
            bds.minY + bds.height / 2,
            bds.width,
            bds.height,
            {
              label: shape.id,
              inertia: Infinity,
              frictionAir: 0.1,
              collisionFilter: { category, mask: ~0 },
            }
          )
          World.add(engine.world, box)
        }
      }
      appState.send('APPLY_FORCES', { bodies: engine.world.bodies })
      // console.log('tick', engine.world.bodies[0].position.y)
    }
    const int = setInterval(() => tick(), 1000 / 60)
    return () => {
      clearInterval(int)
    }
  }, [])

  React.useEffect(() => {
    const api = new Api(appState)
    onMount?.(api)
    window['api'] = api
    function drawTree() {
      api.reset()
      appState.send('CREATE_NODE_SHAPE', {
        pos: [450, 150],
        name: 'someName',
        proofTree,
      })
    }
    function setupStuff() {
      axios
        .get('http://192.168.1.185:3001/getTypes')
        .then((res) => {
          const proofTree: ProofTree = res.data.data
          const id = Number(res.data.id)
          if (id > lastId) {
            api.reset()
            lastId = id
            appState.send('CREATE_NODE_SHAPE', {
              pos: [450, 150],
              name: 'someName',
              proofTree,
            })

            /*            let i = 0
            for (const hyp of data) {
              console.log('dbg type', toGoodFormat(hyp.type))
              for (const name of hyp.names) {
                if (i < 10) {
                  appState.send('CREATE_NODE_SHAPE', {
                    pos: [450 + 150 * i, 150],
                    name,
                    type: toGoodFormat(hyp.type),
                  })
                  i += 1
                } else {
                  break
                }
              }
            }*/
          }
        })
        .catch((e) => {
          console.log('dbg Error ', e)
        })
      setTimeout(() => setupStuff(), 200)
    }
    setupStuff()
  }, [])

  const hideBounds = appState.isInAny('transformingSelection', 'translating', 'creating')

  const firstShapeId = appState.data.pageState.selectedIds[0]
  const firstShape = firstShapeId ? appState.data.page.shapes[firstShapeId] : null
  const hideResizeHandles = firstShape
    ? appState.data.pageState.selectedIds.length === 1 &&
      (shapeUtils[firstShape.type] as any).hideResizeHandles
    : false

  const numGhosts = Object.values(appState.data.page.shapes).filter((s) => s.isGhost).length

  return (
    <AppContainer>
      <canvas id="mcanvas" className="tl-overlay" style={{ zIndex: 200 }}></canvas>
      <Renderer
        shapeUtils={shapeUtils} // Required
        page={appState.data.page} // Required
        pageState={appState.data.pageState} // Required
        performanceMode={appState.data.performanceMode}
        meta={appState.data.meta}
        snapLines={appState.data.overlays.snapLines}
        eraseLine={appState.data.overlays.eraseLine}
        onPointShape={onPointShape}
        onPointBounds={onPointBounds}
        onPointCanvas={onPointCanvas}
        onPointerDown={onPointerDown}
        onPointerMove={onPointerMove}
        onHoverShape={onHoverShape}
        onUnhoverShape={onUnhoverShape}
        onPointBoundsHandle={onPointBoundsHandle}
        onPointHandle={onPointHandle}
        onPan={onPan}
        onPinchStart={onPinchStart}
        onPinchEnd={onPinchEnd}
        onPinch={onPinch}
        onPointerUp={onPointerUp}
        onBoundsChange={onBoundsChange}
        onKeyDown={onKeyDown}
        onKeyUp={onKeyUp}
        onZoom={onZoom}
        hideBounds={hideBounds}
        hideHandles={hideBounds}
        hideResizeHandles={hideResizeHandles}
        hideIndicators={hideBounds}
        hideBindingHandles={true}
      />
      <Toolbar
        activeStates={appState.active}
        lastEvent={appState.data.pageState.camera.zoom + ''}
      />
      <TitleLinks />
    </AppContainer>
  )
}

const AppContainer = styled('div', {
  position: 'fixed',
  top: '0px',
  left: '0px',
  right: '0px',
  bottom: '0px',
  width: '100%',
  height: '100%',
  zIndex: 101,
})
