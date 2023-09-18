import { TLUiMenuSchema, TLUiOverrides } from "@tldraw/tldraw";
import copyTextToClipboard from "src/library/copyTextToClipboard";

const uiOverrides: TLUiOverrides = {
  contextMenu: (editor, schema : TLUiMenuSchema, helpers): TLUiMenuSchema => {
    // This would be perfect, however it doesn't work.
    // (See https://github.com/tldraw/tldraw/issues/1844#issuecomment-1723769497.)
    //
    // const shape = editor.getShapeAtPoint(editor.inputs.currentPagePoint);
    // if (!(shape && shape.type === "customNode")) {
    //   return [];
    // }

    return [
      {
        id: '1',
        type: 'item',
        readonlyOk: true,
        disabled: false,
        checked: false,
        actionItem: {
          id: "2",
          readonlyOk: true,
          label: "Copy" as any,
          onSelect: () => {
            const shape = editor.onlySelectedShape;
            if (shape && "text" in shape.props) {
              const textToCopy = shape.props.text.replace(/🎉/g, '').trim();
              copyTextToClipboard(textToCopy);
             // This is not ideal, we're just not sure how to *not render this contextMeny altogether* if we didn't select anything.
            } else {
              copyTextToClipboard('');
            }
          }
        },
      }
    ]
  }
}

export default uiOverrides;
