import createArrows from './createArrows';
import createNode from './createNode';
import createWindow from './createWindow';
import createWindowInsides from './createWindowInsides';

// lakesare: this is the only exception for our exporting rule right now, theoretically we want `export default { createArrows, ... }`. And we'll want to use it as `CreateElement.arrows` (or `Element.createArrows`), even from within `createWindow.ts` files.
export { createArrows, createNode, createWindow, createWindowInsides };
