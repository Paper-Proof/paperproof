import * as React from "react"
import { getArrow } from "perfect-arrows"

interface PerfectArrowProps {
  p1: { x: number, y: number },
  p2: { x: number, y: number }
}

const PerfectArrow = (props: PerfectArrowProps) => {
  const arrow = getArrow(props.p1.x, props.p1.y, props.p2.x, props.p2.y, {
    padStart: 0, padEnd: 8,
    stretch: 0,
  });
  const [sx, sy, cx, cy, ex, ey, ae, as, ec] = arrow;
  const endAngleAsDegrees = ae * (180 / Math.PI);
  
  // Calculate bounds for viewBox
  const padding = 8;
  const minX = Math.min(sx, cx, ex, props.p1.x, props.p2.x) - padding;
  const minY = Math.min(sy, cy, ey, props.p1.y, props.p2.y) - padding;
  const maxX = Math.max(sx, cx, ex, props.p1.x, props.p2.x) + padding;
  const maxY = Math.max(sy, cy, ey, props.p1.y, props.p2.y) + padding;
  
  const width = maxX - minX;
  const height = maxY - minY;
  
  return (
    <svg
      className="perfect-arrow"
      viewBox={`${minX} ${minY} ${width} ${height}`}
      style={{ 
        position: "absolute",
        top: minY, left: minX,
        width: width, height: height,
        pointerEvents: "none"
      }}
    >
      {/* line */}
      <path d={`M${sx},${sy} Q${cx},${cy} ${ex},${ey}`} strokeWidth="2"/>
      {/* arrow */}
      <polygon
        points="0,-3 6,0, 0,3"
        transform={`translate(${ex},${ey}) rotate(${endAngleAsDegrees})`}
      />
    </svg>
  )
}

export default PerfectArrow;
