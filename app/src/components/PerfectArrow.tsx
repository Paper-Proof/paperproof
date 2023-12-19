import * as React from "react"
import { getArrow } from "perfect-arrows"

interface PerfectArrowProps {
  p1: { x: number, y: number },
  p2: { x: number, y: number }
}

const PerfectArrow = (props: PerfectArrowProps) => {
  const arrow = getArrow(props.p1.x, props.p1.y, props.p2.x, props.p2.y, {
    padEnd: 15,
    stretch: 0,
  })

  const [sx, sy, cx, cy, ex, ey, ae, as, ec] = arrow

  const endAngleAsDegrees = ae * (180 / Math.PI)

  return (
    <svg
      className="perfect-arrow"
      viewBox="0 0 1000 1000"
      style={{ width: 1000, height: 1000 }}
      stroke="#000"
      fill="#000"
      strokeWidth={3}
    >
      <circle cx={sx} cy={sy} r={4}/>
      <path d={`M${sx},${sy} Q${cx},${cy} ${ex},${ey}`} fill="none"/>
      <polygon
        points="0,-6 12,0, 0,6"
        transform={`translate(${ex},${ey}) rotate(${endAngleAsDegrees})`}
      />
    </svg>
  )
}

export default PerfectArrow;
