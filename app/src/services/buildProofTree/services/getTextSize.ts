import { Editor } from "@tldraw/tldraw";

const getTextSize = (editor : Editor, text: string): [number, number] => {
  const size = editor.textMeasure.measureText(text, {
    // used to be TEXT_PROPS, but not exported anymore from tldraw
    // ...TEXT_PROPS,
    lineHeight: 1.35,
    fontWeight: 'normal',
    // fontVariant: 'normal',
    fontStyle: 'normal',
    maxWidth: 'auto',

    // Here we write "tldraw_mono, monospace", but in `editor.createShapes` we need to write "mono"
    fontFamily: '"tldraw_mono", monospace',
    fontSize: 24,
    width: "fit-content",
    padding: "16px",
  });
  return [
    size.w,
    size.h,
  ];
}

export default getTextSize;
