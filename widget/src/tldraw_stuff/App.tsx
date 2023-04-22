import { useStateDesigner } from '@state-designer/react'
import {
  Renderer,
  TLBounds,
  TLKeyboardEventHandler,
  TLPinchEventHandler,
  TLPointerEventHandler,
  TLWheelEventHandler,
} from '@tldraw/core'
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
import { ProofTree } from "shapes/node";
import { Api } from "state/api";
import styled from "./stitches.config";
import { getShapeUtils, shapeUtils } from "./shapes";
import { machine } from "./state/machine";
// import './styles.css'

declare const window: Window & { api: Api };

const onHoverShape: TLPointerEventHandler = (info, e) => {
  machine.send("HOVERED_SHAPE", info);
};

const onUnhoverShape: TLPointerEventHandler = (info, e) => {
  machine.send("UNHOVERED_SHAPE", info);
};

const onPointShape: TLPointerEventHandler = (info, e) => {
  machine.send("POINTED_SHAPE", info);
};

const onPointCanvas: TLPointerEventHandler = (info, e) => {
  machine.send("POINTED_CANVAS", info);
};

const onPointBounds: TLPointerEventHandler = (info, e) => {
  machine.send("POINTED_BOUNDS", info);
};

const onPointHandle: TLPointerEventHandler = (info, e) => {
  machine.send("POINTED_HANDLE", info);
};

const onPointerDown: TLPointerEventHandler = (info, e) => {
  machine.send("STARTED_POINTING", info);
};

const onPointerUp: TLPointerEventHandler = (info, e) => {
  machine.send("STOPPED_POINTING", info);
};

const onPointerMove: TLPointerEventHandler = (info, e) => {
  machine.send("MOVED_POINTER", info);
};

const onPan: TLWheelEventHandler = (info, e) => {
  machine.send("PANNED", info);
};

const onPinchStart: TLPinchEventHandler = (info, e) => {
  machine.send("STARTED_PINCHING", info);
};

const onPinch: TLPinchEventHandler = (info, e) => {
  machine.send("PINCHED", info);
};

const onPinchEnd: TLPinchEventHandler = (info, e) => {
  machine.send("STOPPED_PINCHING", info);
};

const onZoom: TLWheelEventHandler = (info, e) => {
  machine.send("ZOOM_BY", info);
};

const onPointBoundsHandle: TLPinchEventHandler = (info, e) => {
  machine.send("POINTED_BOUNDS_HANDLE", info);
};

const onBoundsChange = (bounds: TLBounds) => {
  machine.send("RESIZED", { bounds });
};

interface AppProps {
  onMount?: (api: Api) => void;
  proofTree?: ProofTree;
}

let lastId = 0;

export default function App({ onMount }: AppProps) {
  const appState = useStateDesigner(machine);

  React.useEffect(() => {
    const engine = Engine.create();
    engine.gravity = { x: 0, y: 0, scale: 1 };
    Runner.run(engine);

    const utils = getShapeUtils("node");
    const canvas = document.getElementsByClassName("tl-canvas");

    const render = Render.create({
      canvas: document.getElementById("mcanvas") as HTMLCanvasElement,
      engine,
      options: { wireframeBackground: "transparent" },
    });
    function setRenderSize() {
      render.options.width = window.innerWidth;
      render.options.height = window.innerHeight;
      render.canvas.width = window.innerWidth;
      render.canvas.height = window.innerHeight;
    }
    setRenderSize();
    window.addEventListener("resize", setRenderSize);

    const FUNCTION_CATEGORY = 0b1;
    const OBJECT_CATEGORY = 0b10;
    const MOUSE_CATEGORY = 0b100;

    Render.run(render);
    const mouse = Mouse.create(canvas[0] as HTMLElement);
    const constraint = MouseConstraint.create(engine, { mouse });
    constraint.collisionFilter.category = MOUSE_CATEGORY;
    World.add(engine.world, constraint);
    Events.on(constraint, "startdrag", (e) => {
      e.body.collisionFilter.mask = ~0 ^ FUNCTION_CATEGORY;
    });
    Events.on(constraint, "enddrag", (e) => {
      e.body.collisionFilter.mask = ~0;
    });
    Events.on(engine, "afterUpdate", () => {
      const { point, zoom } = appState.data.pageState.camera;
      render.options.hasBounds = true;
      render.bounds.min.x = -point[0];
      render.bounds.min.y = -point[1];
      render.bounds.max.x = render.bounds.min.x + window.innerWidth / zoom;
      render.bounds.max.y = render.bounds.min.y + window.innerHeight / zoom;
      constraint.mouse.offset = { x: -point[0], y: -point[1] };
      constraint.mouse.scale = { x: 1 / zoom, y: 1 / zoom };
      if (appState.data.overlays.eraseLine.length > 0) {
        constraint.collisionFilter.mask = 0;
      } else {
        constraint.collisionFilter.mask = ~0;
      }
    });

    // const tick = () => {
    //   const shapes = Object.values(appState.data.page.shapes)
    //   for (const shape of shapes) {
    //     if (shape.type !== 'node') {
    //       continue
    //     }
    //     for (const body of engine.world.bodies) {
    //       if (!shapes.some((s) => s.id == body.label)) {
    //         World.remove(engine.world, body)
    //       }
    //     }
    //     if (!engine.world.bodies.some((b) => b.label == shape.id)) {
    //       const bds = utils.getBounds(shape)
    //       const category =
    //         shape.vars.length > 0 && shape.vars[0].startsWith('∀')
    //           ? FUNCTION_CATEGORY
    //           : OBJECT_CATEGORY
    //       const box = Bodies.rectangle(
    //         bds.minX + bds.width / 2,
    //         bds.minY + bds.height / 2,
    //         bds.width,
    //         bds.height,
    //         {
    //           label: shape.id,
    //           inertia: Infinity,
    //           frictionAir: 0.1,
    //           collisionFilter: { category, mask: ~0 },
    //         }
    //       )
    //       World.add(engine.world, box)
    //     }
    //   }
    //   appState.send('APPLY_FORCES', { bodies: engine.world.bodies })
    //   // console.log('tick', engine.world.bodies[0].position.y)
    // }
    // const int = setInterval(() => tick(), 1000 / 60)
    // return () => {
    //   clearInterval(int)
    // }
  }, []);

  React.useEffect(() => {
    const api = new Api(appState);
    onMount?.(api);
    window["api"] = api;
    // antonkov: Extremely weird, but without another setInterval before setupStuff interval would only be called once
    setInterval(() => console.log("Super weird"), 100 * 1000 * 1000);
    function setupStuff() {
      fetch("getTypes")
        .then((response) => response.json())
        .then((res) => {
          const proofTree: ProofTree = res.data;
          const id = Number(res.id);
          console.log(id);
          if (id > lastId) {
            api.selectAll();
            api.delete();
            api.createShapes(
              {
                type: "node",
                id: "proofTree",
                point: [450, 150],
                proofTree,
              },
              { type: "node", point: [100, 100], vars: ["p", "q", "r"] }
            );
            lastId = id;
          }
        })
        .catch((e) => {
          console.log("dbg Error ", e);
        });
    }
    const int = setInterval(() => setupStuff(), 200);
    return () => clearInterval(int);
  }, []);

  return (
    <AppContainer>
      <canvas // For rendering what the physics engine sees
        id="mcanvas"
        className="tl-overlay"
        style={{ zIndex: 200 }}
      ></canvas>
      <Renderer
        shapeUtils={shapeUtils} // Required
        page={appState.data.page} // Required
        pageState={appState.data.pageState} // Required
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
        onZoom={onZoom}
        hideResizeHandles={true}
        hideBindingHandles={true}
      />
    </AppContainer>
  );
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