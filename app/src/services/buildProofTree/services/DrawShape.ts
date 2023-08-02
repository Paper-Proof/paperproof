import { Editor as App, TLShapeId, TLParentId, createShapeId } from "@tldraw/tldraw";

const drawShapeArrow = (app: App, fromId: TLShapeId, toId: TLShapeId) => {
  app.createShapes([
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

const drawShapeTactic = (app: App,
  id: TLShapeId, parentId: TLParentId | undefined,
  x: number, y: number, w: number, h: number, text: string
) => {
  app.createShapes([
    {
      id, type: "geo", x, y, parentId,
      props: {
        geo: "rectangle", font: "mono", size: "m", w, h, text,

        dash: "dotted",
        fill: "none",
        color: "grey",
      },
    },
  ]);
}

const drawShapeGoal = (app: App,
  id: TLShapeId, parentId: TLParentId | undefined,
  x: number, y: number, w: number, h: number, text: string
) => {
  app.createShapes([
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

const drawShapeHypothesis = (app: App,
  id: TLShapeId, parentId: TLParentId | undefined,
  x: number, y: number, w: number, h: number, text: string
) => {
  app.createShapes([
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

// Our actual window
const drawShapeWindow = (app: App,
  id: TLShapeId, parentId: TLParentId | undefined,
  x: number, y: number, w: number, h: number, depth: number,
  goalUsername: string | null, goalUsernameHeight: number
) => {
  app.createShapes([
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

// Temporary window
// const drawShapeWindow = (app: App,
//   id: TLShapeId, parentId: TLParentId | undefined,
//   x: number, y: number, w: number, h: number, depth: number,
//   goalUsername: string | null, goalUsernameHeight: number
// ) => {
//   app.createShapes([
//     {
//       id,
//       type: "frame",
//       x,
//       y,
//       parentId,
//       props: { w, h },
//     },
//   ]);
// }

export { drawShapeArrow, drawShapeTactic, drawShapeGoal, drawShapeHypothesis, drawShapeWindow };
