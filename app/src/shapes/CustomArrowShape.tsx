import { TLArrowUtil, TLArrowShape, TLBaseShape, defineShape, App } from '@tldraw/tldraw';
import {VecLike} from '@tldraw/primitives'

type CustomArrowShapeType = TLBaseShape<'customArrow', {}>;

type ArrowPoint = {point: VecLike};
type ArrowInfo = {start: ArrowPoint, end: ArrowPoint};

const getIfVerticalDistanceBetweenNodesIs0 = (arrowInfo: ArrowInfo|undefined) => {
  if (!arrowInfo) return null
  const from = arrowInfo.start.point;
  const to = arrowInfo.end.point;
  const verticalDistance = Math.abs(from.y - to.y);
  return verticalDistance === 0;
}

const doLinesIntersect = (start1: number, end1: number, start2: number, end2: number) => (
  (start1 >= start2 && start1 <= end2) ||
  (start2 >= start1 && start2 <= end1)
);

const getIfNodesTouch = (arrowShape: TLArrowShape, app: App) => {
  if (arrowShape.props.start.type === "binding" && arrowShape.props.end.type === "binding") {
    const fromNodeBounds = app.getBoundsById(arrowShape.props.start.boundShapeId);
    const toNodeBounds = app.getBoundsById(arrowShape.props.end.boundShapeId);

    const fromNode = app.getShapeById(arrowShape.props.start.boundShapeId);
    const toNode = app.getShapeById(arrowShape.props.end.boundShapeId);

    if (fromNode && fromNodeBounds && toNode && toNodeBounds) {
      const nodesTouch = doLinesIntersect(fromNode.x, fromNode.x + fromNodeBounds.w, toNode.x, toNode.x + toNodeBounds.w);
      return nodesTouch;
    }
    return null;
  }
  return null;
}

class CustomArrowUtil extends TLArrowUtil {
  static override type = "customArrow";

  override render(arrowShape: TLArrowShape) {
    // Important to store it here and not later
    const superRender = super.render(arrowShape);

    const ifVerticalDistanceBetweenNodesIs0 = getIfVerticalDistanceBetweenNodesIs0(super.getArrowInfo(arrowShape));
    const ifNodesTouch = getIfNodesTouch(arrowShape, this.app);
    // If we couldn't find some info, just relay handling to the original component
    if (ifVerticalDistanceBetweenNodesIs0 === null || ifNodesTouch === null) return superRender;
    // Don't show the arrow when the nodes are super close
    if (ifVerticalDistanceBetweenNodesIs0 && ifNodesTouch) return null;
    return superRender;
  }
}

// @anton probably a suboptimal way to inherit stuff/type stuff, tell me if you have better ideas
export const CustomArrowShape = defineShape<CustomArrowShapeType>({
  type: "customArrow",
  getShapeUtil: () => CustomArrowUtil as any,
  // TODO:lakesare These should be here?
  // validator: arrowShapeTypeValidator,
  // migrations: arrowShapeMigrations,
});
