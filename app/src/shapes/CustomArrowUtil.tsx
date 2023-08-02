import { ArrowShapeUtil, TLArrowShape, Editor } from '@tldraw/tldraw';

const getIfVerticalDistanceBetweenNodesIs0 = (arrowInfo: any) => {
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

const getIfNodesTouch = (arrowShape: TLArrowShape, editor: Editor) => {
  if (arrowShape.props.start.type === "binding" && arrowShape.props.end.type === "binding") {
    const fromNodeBounds = editor.getPageBounds(arrowShape.props.start.boundShapeId)
    const toNodeBounds = editor.getPageBounds(arrowShape.props.end.boundShapeId);

    const fromNode = editor.getShape(arrowShape.props.start.boundShapeId);
    const toNode = editor.getShape(arrowShape.props.end.boundShapeId);

    if (fromNode && fromNodeBounds && toNode && toNodeBounds) {
      const nodesTouch = doLinesIntersect(fromNode.x, fromNode.x + fromNodeBounds.w, toNode.x, toNode.x + toNodeBounds.w);
      return nodesTouch;
    }
    return null;
  }
  return null;
}

export default class CustomArrowUtil extends ArrowShapeUtil {
  static override type = 'customArrow' as const

  override component(arrowShape: TLArrowShape) {
    // Important to store it here and not later
    const superRender = super.component(arrowShape);

    const ifVerticalDistanceBetweenNodesIs0 = getIfVerticalDistanceBetweenNodesIs0(this.editor.getArrowInfo(arrowShape)!);
    const ifNodesTouch = getIfNodesTouch(arrowShape, this.editor);
    // If we couldn't find some info, just relay handling to the original component
    if (ifVerticalDistanceBetweenNodesIs0 === null || ifNodesTouch === null) return superRender;
    // Don't show the arrow when the nodes are super close
    if (ifVerticalDistanceBetweenNodesIs0 && ifNodesTouch) return null;
    return superRender;
  }
}
