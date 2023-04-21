import {
  HTMLContainer,
  SVGContainer,
  TLComponentProps,
  TLShapeUtil,
} from "@tldraw/core";
import Vec from "@tldraw/vec";
import * as React from "react";
import { Layout } from "react-feather";
import { FrameShape, NodeShape, ProofTree } from "./NodeShape";

interface Color {
  h: number;
  s: number;
  l: number;
}

interface Rect {
  center: number[];
  size: number[];
  text: string;
  color: Color;
  kf: number;
}

const newColors = [
  "rgba(219,240,224,255)",
  "rgba(244,218,219,255)",
  "rgba(249,240,230,255)",
  "rgba(221,237,250,255)",
  "rgba(245,234,250,255)",
].reverse();
// const colors: { [key: string]: string } = {}

function hash(text: string) {
  let hash = 0;
  if (text.length === 0) return hash;
  for (let i = 0; i < text.length; i++) {
    const chr = text.charCodeAt(i);
    hash = (hash << 5) - hash + chr;
    hash |= 0; // Convert to 32bit integer
  }
  return hash;
}

function getColor(text: string) {
  const h = hash(text + "abac");
  return { h: Math.abs(h * 107) % 360, s: 58 + (h % 18), l: 90 + (h % 5) };
}

function createRect(
  p: number[],
  sz: number[],
  text: string,
  type: "exists" | "forall"
): Rect {
  return {
    center: p.slice(),
    size: sz.slice(),
    text,
    color: getColor(text),
    kf: type == "forall" ? 0.4 : 0.6,
  };
}

function genRectsForSize(
  size: number[],
  text: string[],
  name?: string
): Rect[] {
  const pad = [5, 5];
  let p = [0, 0];
  let sz = [80, 25];
  const rects: Rect[] = [
    createRect(
      p,
      sz,
      text.length == 1 ? `${name}: ${text[0]}` : text[0],
      "exists"
    ),
  ];
  for (let i = 0; i < text.length - 1; i++) {
    if (text[i + 1].includes("∀")) {
      p = [p[0] - pad[0], p[1] - sz[1]];
      sz = [sz[0] + 2 * pad[0], sz[1] * 2 + pad[1]];
      rects.push(createRect(p, sz, text[i + 1], "forall"));
    } else {
      const k = 0.7;
      p = [p[0] - sz[0] * k - pad[0], p[1]];
      rects.push(createRect(p, [sz[0] * k, sz[1]], text[i + 1], "exists"));
      sz = [sz[0] * (1 + k) + pad[0], sz[1]];
    }
  }
  for (const rect of rects) {
    rect.center = Vec.sub(rect.center, p);
    rect.center = Vec.divV(Vec.mulV(rect.center, size), sz);
    rect.size = Vec.divV(Vec.mulV(rect.size, size), sz);
  }
  return rects;
}

export function getRects(text: string[], name?: string): [number[], Rect[]] {
  const size: Vec2 =
    text.length == 1
      ? [120, 100]
      : text[text.length - 1].includes("∀")
      ? [175, 100]
      : [300, 100];
  return [size, genRectsForSize(size, text, name)];
}

function hsla(color: Color): string {
  return `hsla(${color.h}, ${color.s}%, ${color.l}%, 1)`;
}

interface ProofLayout {
  expanded: boolean;
  size: [number, number];
  name: string;
  action: string;
  endType: string;
  intros: string[];
  defns: string[];
  children: ProofLayout[];
}

function scaleLayout(layout: ProofLayout, scale: number) {
  layout.size = [layout.size[0] * scale, layout.size[1] * scale];
  for (const child of layout.children) {
    scaleLayout(child, scale);
  }
}

function scaleLayoutToFit(layout: ProofLayout, size: [number, number]) {
  const scale = Math.min(size[0] / layout.size[0], size[1] / layout.size[1]);
  scaleLayout(layout, scale);
}

/** Draws a proof tree starting with pos as a bottom left corner and returns drawn rects. */
function buildProofLayout(tree: ProofTree, intros: string[] = []): ProofLayout {
  if (tree.action?.includes("intro")) {
    const intros = tree.children.flatMap((c) =>
      "type" in c ? [`(${c.name}: ${c.type})`] : []
    );
    return buildProofLayout(tree.children[0] as ProofTree, intros);
  }
  const children = (tree.children ?? []).flatMap((child) =>
    "type" in child ? [] : buildProofLayout(child)
  );
  const defns = (tree.children ?? []).flatMap((child) =>
    "type" in child && child.name.includes(":=") ? [child.name] : []
  );
  const sizes = children.map((c) => c.size);
  const size = sizes.reduce(
    ([x0, y0], [x, y]) => [x0 + x + 10, Math.max(y0, y)],
    [10, 0]
  );
  return {
    expanded: true,
    size: [
      Math.max(100, size[0]),
      Math.max(50, size[1] + 50 + (intros.length > 0 ? 30 : 0)),
    ],
    endType: tree.fromType,
    action: tree.action,
    name: tree.name,
    intros,
    defns,
    children,
  };
}

const forallSymbol = "∀";

type Events = TLComponentProps<NodeShape, SVGSVGElement, any>["events"];
type Vec2 = [number, number];

export const TypeComponent = ({
  pos,
  size,
  name,
  vars,
}: {
  pos: number[];
  size: number[];
  name: string;
  vars: string[];
}) => {
  return (
    <>
      {genRectsForSize(size, [...vars].reverse(), name)
        .reverse()
        .map((shape, index) => {
          const [fontSize, textY] = (() => {
            const fontSize1 = shape.size[1] * 0.4;
            const fontSize2 = ((shape.size[0] - 20) * 3) / shape.text.length;
            if (fontSize1 < fontSize2) {
              return [fontSize1, shape.size[1] * shape.kf];
            } else {
              return [
                fontSize2,
                shape.size[1] * (shape.kf < 0.5 ? 0.3 : shape.kf),
              ];
            }
          })();
          const center = [
            pos[0] + shape.center[0] + 5,
            pos[1] + shape.center[1] - size[1] + 5,
          ];
          return (
            <g key={index}>
              <rect
                x={center[0]}
                y={center[1]}
                width={shape.size[0]}
                height={shape.size[1]}
                rx={5}
                stroke={hsla({ ...shape.color, l: 50 })}
                strokeWidth={1}
                strokeLinejoin="round"
                fill={hsla(shape.color)}
                pointerEvents="all"
              />
              <text
                x={center[0] + 10}
                y={center[1] + +textY}
                fill="black"
                textLength={shape.size[0] - 20}
                lengthAdjust="spacing"
                fontSize={fontSize}
                style={{ userSelect: "none" }}
              >
                {shape.text}
              </text>
            </g>
          );
        })}
    </>
  );
};

export const FrameComponent = ({
  layout,
  pos,
  events,
}: {
  layout: ProofLayout;
  pos: [number, number];
  events: Events;
}) => {
  const [expanded, setExpanded] = React.useState(true);

  const childrenPos: [number, number][] = [];
  let curX: number = pos[0] + 10;
  for (const child of layout.children) {
    childrenPos.push([curX, pos[1] - 40]);
    curX += child.size[0] + 10;
  }
  const rect = (
    <rect
      x={pos[0] + 5}
      y={pos[1] - layout.size[1] + 5}
      width={layout.size[0] - 10}
      height={layout.size[1] - 10}
      stroke={hsla({ ...getColor(layout.endType), l: 50 })}
      strokeWidth={1}
      rx={5}
      strokeLinejoin="round"
      fill={hsla(getColor(layout.endType))}
    ></rect>
  );
  if (expanded) {
    return (
      <>
        <g {...events} onClick={() => setExpanded(!expanded)}>
          {rect}
          {layout.intros.length > 0 || layout.defns.length > 0 ? (
            <text x={pos[0] + 10} y={pos[1] - layout.size[1] + 30}>
              {layout.intros.length > 0
                ? `${forallSymbol} ${layout.intros.join(", ")}`
                : ""}
              {layout.defns.length > 0 ? `${layout.defns.join(", ")}` : ""}
            </text>
          ) : (
            <> </>
          )}
          <text x={pos[0] + 10} y={pos[1] - 15} fill={"black"} fontSize={12}>
            {layout.name}: {layout.endType}
          </text>
          <text x={pos[0] + 10} y={pos[1] - 30} fill={"grey"} fontSize={12}>
            {layout.action}
          </text>
        </g>
        {(expanded ? layout.children : []).map((child, index) => (
          <FrameComponent
            layout={child}
            pos={childrenPos[index]}
            events={events}
          ></FrameComponent>
        ))}
      </>
    );
  } else {
    return (
      <g {...events} onClick={() => setExpanded(!expanded)}>
        <TypeComponent
          name={"hello"}
          pos={Vec.sub(pos, [0, 10])}
          size={Vec.sub(layout.size, [10, 10])}
          vars={[
            ...layout.intros.map((s) => `${forallSymbol} ${s}`),
            layout.endType,
          ]}
        ></TypeComponent>
      </g>
    );
    /*   return (
      <g {...events} onClick={() => setExpanded(!expanded)}>
        {rect}
        {layout.intros.length > 0 ? (
          <text x={pos[0] + 50} y={pos[1] - layout.size[1] + 30} fontSize={25}>
            {forallSymbol} {layout.intros.join(', ')}
          </text>
        ) : (
          <> </>
        )}
        <text x={pos[0] + 50} y={pos[1] - 15} fill={'black'} fontSize={25}>
          {layout.endType}
        </text>
      </g>
    )*/
  }
};
export const NodeComponent = TLShapeUtil.Component<NodeShape, SVGSVGElement>(
  ({ shape, events }: TLComponentProps<NodeShape, SVGSVGElement, any>, ref) => {
    if (shape.proofTree) {
      const layout = buildProofLayout(shape.proofTree);
      scaleLayoutToFit(layout, [800, 500]);
      return (
        <SVGContainer ref={ref} {...events} pointerEvents="all">
          <FrameComponent
            layout={layout}
            pos={[0, 500]}
            events={events}
          ></FrameComponent>
        </SVGContainer>
      );
    }

    const color = !shape.proofTree ? "white" : "black";

    return (
      <SVGContainer ref={ref} {...events}>
        {getRects([...shape.vars].reverse(), shape.name)[1]
          .reverse()
          .map((shape, index) => {
            const [fontSize, textY] = (() => {
              const fontSize1 = shape.size[1] * 0.4;
              const fontSize2 = ((shape.size[0] - 20) * 3) / shape.text.length;
              if (fontSize1 < fontSize2) {
                return [fontSize1, shape.size[1] * shape.kf];
              } else {
                return [
                  fontSize2,
                  shape.size[1] * (shape.kf < 0.5 ? 0.3 : shape.kf),
                ];
              }
            })();
            return (
              <g key={index}>
                <rect
                  x={shape.center[0]}
                  y={shape.center[1]}
                  width={shape.size[0]}
                  height={shape.size[1]}
                  rx={5}
                  stroke={hsla({ ...shape.color, l: 50 })}
                  strokeWidth={1}
                  strokeLinejoin="round"
                  fill={hsla(shape.color)}
                  pointerEvents="all"
                />
                <text
                  x={shape.center[0] + 10}
                  y={shape.center[1] + +textY}
                  fill="black"
                  textLength={shape.size[0] - 20}
                  lengthAdjust="spacing"
                  fontSize={fontSize}
                  style={{ userSelect: "none" }}
                >
                  {shape.text}
                </text>
              </g>
            );
          })}
      </SVGContainer>
    );
  }
);
