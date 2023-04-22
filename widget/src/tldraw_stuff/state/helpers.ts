import type { TLPageState } from "@tldraw/core";
import Vec from "@tldraw/vec";

export function getPagePoint(point: number[], pageState: TLPageState) {
  return Vec.sub(Vec.div(point, pageState.camera.zoom), pageState.camera.point);
}
