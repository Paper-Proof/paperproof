import { Editor, TLShapeId, TLParentId, createShapeId } from "@tldraw/tldraw";

const arrow = (editor: Editor, fromId: TLShapeId, toId: TLShapeId) => {
  editor.createShapes([
    {
      id: createShapeId(),
      type: "customArrow",
      props: {
        start: {
          type: 'binding', boundShapeId: fromId,
          normalizedAnchor: { x: 0.5, y: 1 },
          isExact: true
        },
        end: {
          type: 'binding', boundShapeId: toId,
          normalizedAnchor: { x: 0.5, y: 0 },
          isExact: true
        },
        color: "grey",
      },
    },
  ]);
}

const tactic = (editor: Editor,
  id: TLShapeId, parentId: TLParentId | undefined,
  x: number, y: number, w: number, h: number, text: string
) => {
  editor.createShapes([
    {
      id, type: "customNode", x, y, parentId,
      props: {
        geo: "rectangle", font: "mono", size: "m", w, h, text,

        dash: "dotted",
        fill: "solid",
        color: "grey",
      },
      // probably better as a separate shape
      meta: {
        isTactic: true
      }
    },
  ]);
}

const goal = (editor: Editor,
  id: TLShapeId, parentId: TLParentId | undefined,
  x: number, y: number, w: number, h: number, text: string
) => {
  editor.createShapes([
    {
      id, type: "customNode", x, y, parentId,
      props: {
        geo: "rectangle", font: "mono", size: "m", w, h, text,

        dash: "solid",
        fill: "solid",
        color: "light-red"
      },
    },
  ]);
}

const hypothesis = (editor: Editor,
  id: TLShapeId, parentId: TLParentId | undefined,
  x: number, y: number, w: number, h: number, text: string
) => {
  editor.createShapes([
    {
      id, type: "customNode", x, y, parentId,
      props: {
        geo: "rectangle", font: "mono", size: "m", w, h, text,

        dash: "solid",
        fill: "solid",
        color: "light-green"
      },
    },
  ]);
}

const window = (editor: Editor,
  id: TLShapeId, parentId: TLParentId | undefined,
  x: number, y: number, w: number, h: number, depth: number,
  goalUsername: string | null, goalUsernameHeight: number
) => {
  editor.createShapes([
    {
      id,
      type: "window",
      x,
      y,
      parentId,
      props: { w, h, depth, goalUsername, goalUsernameHeight },
    },
  ]);
}

export default { arrow, tactic, goal, hypothesis, window };
