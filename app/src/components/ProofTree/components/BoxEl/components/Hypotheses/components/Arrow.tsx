import * as React from "react"
import { getArrow } from "perfect-arrows"

const PerfectArrow = () => {
  const p1 = { x: 64, y: 64 }
  const p2 = { x: 128, y: 96 }

  const arrow = getArrow(p1.x, p1.y, p2.x, p2.y, {
    padEnd: 20,
  })

  const [sx, sy, cx, cy, ex, ey, ae, as, ec] = arrow

  const endAngleAsDegrees = ae * (180 / Math.PI)

  return (
    <svg
      viewBox="0 0 720 480"
      style={{ width: 720, height: 480 }}
      stroke="#000"
      fill="#000"
      strokeWidth={3}
    >
      <circle cx={sx} cy={sy} r={4} />
      <path d={`M${sx},${sy} Q${cx},${cy} ${ex},${ey}`} fill="none" />
      <polygon
        points="0,-6 12,0, 0,6"
        transform={`translate(${ex},${ey}) rotate(${endAngleAsDegrees})`}
      />
    </svg>
  )
}

export default PerfectArrow;
