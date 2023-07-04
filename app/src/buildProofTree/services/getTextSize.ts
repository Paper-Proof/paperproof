import { App, LABEL_FONT_SIZES, TEXT_PROPS } from "@tldraw/tldraw";

export default function getTextSize(app : App, text: string): [number, number] {
  const size = app.textMeasure.measureText({
    ...TEXT_PROPS,
    text,

    // Here we write "tldraw_mono, monospace", but in `app.createShapes` we need to write "mono"
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
