import { TLArrowUtil, TLArrowShape, defineShape } from '@tldraw/tldraw';
import { TLBaseShape } from "@tldraw/tldraw";

type CustomArrowShapeType = TLBaseShape<'customArrow', {}>;

class CustomArrowUtil extends TLArrowUtil {
  static override type = "customArrow";

  override getArrowInfo(shape: TLArrowShape) {
    const arrowInfo = super.getArrowInfo(shape);
    if (!arrowInfo) return arrowInfo;

    const from = arrowInfo.start.point;
    const to = arrowInfo.end.point;

    const verticalLength = Math.abs(from.y - to.y);
    const horizontalLength = Math.abs(from.x - to.x);

    // `.isValid` is usually true iff the length of the arrow is nonzero.
    // (https://github.com/tldraw/tldraw/blob/main/packages/editor/src/lib/editor/shapes/arrow/arrow/straight-arrow.ts#L152)
    // Here, we're making `.isValid` more restrictive - we're hiding the arrow more frequently.
    if (shape.props.start.type === "binding" && shape.props.end.type === "binding") {
      const fromNodeBounds = this.app.getBoundsById(shape.props.start.boundShapeId);

      // TODO:lakesare - arrows in this proof are weird, let's change the logic to "while they still touch there should be no arrow"
      //
      // example(a b : Prop) : a ∧ b → b ∧ a:= by
      // intro ab
      // cases ab
      // apply And.intro <;> assumption
      if (fromNodeBounds && verticalLength === 0 && horizontalLength <= (fromNodeBounds.w / 2)) {
        arrowInfo.isValid = false;
      }
    }

    return arrowInfo;
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
