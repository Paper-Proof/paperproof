import React from "react";

interface Props {
  initialInstructions?: string;
  initialShortenWords?: boolean;
  onConvert: (instructions: string, shortenWords: boolean) => void;
  onCancel: () => void;
}

const SnackbarLatexPrompt = ({ initialInstructions = "", initialShortenWords = false, onConvert, onCancel }: Props) => {
  const [instructions, setInstructions] = React.useState(initialInstructions);
  const [shortenWords, setShortenWords] = React.useState(initialShortenWords);

  return (
    <div className="latex-prompt">
      <div className="latex-prompt-title">Convert to LaTeX</div>
      <textarea
        value={instructions}
        onChange={(e) => setInstructions(e.target.value)}
        placeholder="Additional instructions for the LLM (optional)"
        rows={3}
      />
      <label className="checkbox">
        <input type="checkbox" checked={shortenWords} onChange={(e) => setShortenWords(e.target.checked)}/>
        Shorten long words
      </label>
      <div className="latex-prompt-actions">
        <button className="-cancel" onClick={onCancel}>Cancel</button>
        <button className="-convert" onClick={() => onConvert(instructions, shortenWords)}>Convert</button>
      </div>
    </div>
  );
};

export default SnackbarLatexPrompt;
