import type { S } from '@state-designer/react'
import type { TLBinding, TLPage, TLPageState, TLPerformanceMode, TLSnapLine } from '@tldraw/core'
import type { Shape } from 'shapes'

export const VERSION = 1
export const PERSIST_DATA = false;
export const FIT_TO_SCREEN_PADDING = 100
export const BINDING_PADDING = 12
export const SNAP_DISTANCE = 5

export interface CustomBinding extends TLBinding {
  handleId: 'start' | 'end'
}

export const INITIAL_PAGE: TLPage<Shape, CustomBinding> = {
  id: "page1",
  shapes: {},
  bindings: {},
};

export const INITIAL_PAGE_STATE: TLPageState = {
  id: 'page1',
  selectedIds: [],
  camera: {
    point: [0, 0],
    zoom: 1,
  },
  brush: null,
  pointedId: null,
  hoveredId: null,
  editingId: null,
  bindingId: null,
}

export const INITIAL_DATA = {
  id: "myDocument",
  version: VERSION,
  page: INITIAL_PAGE,
  pageState: INITIAL_PAGE_STATE,
  overlays: {
    eraseLine: [] as TLSnapLine,
  },
};

export type AppDocument = {
  id: string
  page: TLPage<Shape>
}

export type AppData = typeof INITIAL_DATA

export type Action = S.Action<AppData>

export type Condition = S.Condition<AppData>
