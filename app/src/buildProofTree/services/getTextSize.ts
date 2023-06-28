import { App, LABEL_FONT_SIZES, TEXT_PROPS } from "@tldraw/tldraw";

export default function getTextSize(app : App, text: string): [number, number] {
  const size = app.textMeasure.measureText({
    ...TEXT_PROPS,
    text,
    fontFamily: '"tldraw_mono", monospace',
    fontSize: LABEL_FONT_SIZES["m"],
    width: "fit-content",
    padding: "16px",
  });
  return [
    size.w,
    size.h,
  ];
}
