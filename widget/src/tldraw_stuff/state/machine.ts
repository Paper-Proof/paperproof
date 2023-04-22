import { createState } from '@state-designer/react'
import { TLPointerInfo } from '@tldraw/core'
import Vec from '@tldraw/vec'
import * as actions from './actions'
import { INITIAL_DATA } from './constants'
import { mutables } from './mutables'

export const machine = createState({
  data: INITIAL_DATA,
  on: {
    MOVED_POINTER: "updatePointer",
    SELECTED_TOOL: { to: (_, payload) => payload.name },
    STARTED_POINTING: ["setInitialPoint", "setSnapshot"],
    PANNED: "panCamera",
    PINCHED: "pinchCamera",
    ZOOMED_TO_SELECTION: "zoomToSelection",
    ZOOMED_TO_FIT: "zoomToFit",
    ZOOMED_IN: "zoomIn",
    ZOOMED_OUT: "zoomOut",
    ZOOM_BY: "zoomBy",
    RESIZED: "setViewport",
    // These events are called from the API only, see api.ts
    CREATED_SHAPES: ["createShapes"],
    UPDATED_SHAPES: ["updateShapes"],
    DELETED_SHAPES: ["deleteShapes"],
    APPLY_FORCES: ["applyForces"],
  },
  initial: "select",
  states: {
    select: {
      initial: "idle",
      states: {
        idle: {
          onEnter: ["clearPointedShape"],
          on: {
            SELECTED_ALL: "selectAllShapes",
            DESELECTED_ALL: "deselectAllShapes",
            CANCELLED: ["deselectAllShapes"],
            DELETED: ["deleteSelectedShapes"],
            HOVERED_SHAPE: "setHoveredShape",
            UNHOVERED_SHAPE: "clearHoveredShape",
            POINTED_CANVAS: [
              {
                do: "setInitialPoint",
                to: "pointing.canvas",
              },
            ],
            POINTED_SHAPE: [
              {
                unless: "shapeIsSelected",
                do: ["selectShape"],
              },
              { to: "pointing.shape" },
            ],
            POINTED_BOUNDS: {
              to: "pointing.bounds",
            },
          },
        },
        pointing: {
          initial: "canvas",
          states: {
            canvas: {
              on: {
                MOVED_POINTER: ["updateEraseLine", "eraseShapes"],
                STOPPED_POINTING: {
                  do: ["splitGhostShapes", "clearEraseLine"],
                  to: "select.idle",
                },
              },
            },
            bounds: {
              on: {
                MOVED_POINTER: {
                  if: "hasLeftDeadZone",
                  to: "translating.shapes",
                },
                STOPPED_POINTING: {
                  do: "deselectAllShapes",
                  to: "select.idle",
                },
              },
            },
            shape: {
              on: {
                MOVED_POINTER: {
                  if: "hasLeftDeadZone",
                  to: "translating.shapes",
                },
                STOPPED_POINTING: [
                  {
                    if: "shapeIsSelected",
                    do: "selectShape",
                  },
                  {
                    to: "select.idle",
                  },
                ],
              },
            },
          },
        },
        translating: {
          on: {
            CANCELLED: {
              do: "restoreSnapshot",
              to: "select.idle",
            },
            STOPPED_POINTING: {
              do: ["unwrapGhostShape"],
              to: "select.idle",
            },
          },
          initial: "shapes",
          states: {
            shapes: {
              on: {
                // Disable for the physics engine
                TOGGLED_MODIFIER: ["translateSelectedShapes"],
                MOVED_POINTER: ["translateSelectedShapes"],
                PANNED: ["translateSelectedShapes"],
              },
            },
            handle: {},
          },
        },
      },
    },
  },
  conditions: {
    hasLeftDeadZone(data, payload: TLPointerInfo) {
      return Vec.dist(mutables.currentPoint, mutables.initialPoint) > 2;
    },
    shapeIsSelected(data, payload: { target: string }) {
      return data.pageState.selectedIds.includes(payload.target);
    },
    shapeIsPointed(data, payload: { target: string }) {
      return mutables.pointedShapeId === payload.target;
    },
  },
  actions, // See actions folder
});
