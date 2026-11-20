declare global { interface Window { katex?: { renderToString: (tex: string, options?: object) => string } } }

const escapeHtml = (s: string) => s.replace(/&/g, "&amp;").replace(/</g, "&lt;");

export default {
  renderToString: (tex: string, options?: object): string =>
    window.katex ? window.katex.renderToString(tex, options) : `<code>${escapeHtml(tex)}</code>`,
};
