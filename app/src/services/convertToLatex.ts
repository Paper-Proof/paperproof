import { ConvertedProofTree } from "types";

const LATEX_PROXY_URL = "https://paperproof.xyz/api/latex";

const collectTexts = (proofTree: ConvertedProofTree): { stable: string[], changing: string[] } => {
  const textBoxIds = new Map<string, Set<string>>();
  for (const box of proofTree.boxes) {
    for (const goalNode of box.goalNodes) {
      if (goalNode.text) {
        if (!textBoxIds.has(goalNode.text)) textBoxIds.set(goalNode.text, new Set());
        textBoxIds.get(goalNode.text)!.add(box.id);
      }
    }
    for (const hypLayer of box.hypLayers) {
      for (const hypNode of hypLayer.hypNodes) {
        if (hypNode.text) {
          if (!textBoxIds.has(hypNode.text)) textBoxIds.set(hypNode.text, new Set());
          textBoxIds.get(hypNode.text)!.add(box.id);
        }
      }
    }
  }
  const stable: string[] = [];
  const changing: string[] = [];
  for (const [text, boxIds] of textBoxIds) {
    if (boxIds.size > 1) stable.push(text);
    else changing.push(text);
  }
  return { stable, changing };
};

const SHORTEN_INSTRUCTION = "Shorten long operator/function names to intuitive abbreviations (e.g. dirichletKernel → ker, partialSum → psum). Use \\operatorname{abbrev} for the result.";

const SYSTEM_PROMPT = `You convert Lean 4 proof expressions to KaTeX-renderable LaTeX. Rules:
- Only use standard KaTeX-supported commands. Never invent commands like \\ope, \\ker (unless it's the standard \\ker), etc.
- When the user asks to shorten a word or name (e.g. "use ope instead of operator", "ker for dirichletKernel"), render it as \\operatorname{ope}, \\operatorname{ker}, etc. — never as a bare backslash command like \\ope.
- If unsure whether a command exists in KaTeX, use \\operatorname{...} or \\mathrm{...} instead.
- Always strip Lean coercion/conversion arrows (↑, ↓) — these are implementation details of Lean's type system and should not appear in the mathematical output.
- Lean interval notation: render Ioo a b as (a, b) (open-open), Icc a b as [a, b] (closed-closed), Ico a b as [a, b) (closed-open), Ioc a b as (a, b] (open-closed).`;

const convertTextsToLatex = async (texts: string[], instructions: string = "", shortenWords: boolean = false): Promise<Record<string, string>> => {
  if (texts.length === 0) return {};

  const combined = [instructions.trim(), shortenWords ? SHORTEN_INSTRUCTION : ""].filter(Boolean).join("\n");
  const extraInstructions = combined ? `\n\nAdditional instructions: ${combined}` : "";
  const prompt = `Convert each of the following Lean 4 expressions to LaTeX notation. Return ONLY a JSON object where keys are the original expressions exactly as given, and values are the LaTeX equivalents (without surrounding $ delimiters, just the raw LaTeX).${extraInstructions}

Expressions:
${texts.map(t => JSON.stringify(t)).join("\n")}`;

  const response = await fetch(LATEX_PROXY_URL, {
    method: "POST",
    headers: {
      "Content-Type": "application/json",
    },
    body: JSON.stringify({
      model: "gpt-4o",
      messages: [
        { role: "system", content: SYSTEM_PROMPT },
        { role: "user", content: prompt }
      ],
      response_format: { type: "json_object" },
    }),
  });

  if (!response.ok) {
    throw new Error(`OpenAI API error: ${response.status} ${response.statusText}`);
  }

  const data = await response.json();
  return JSON.parse(data.choices[0].message.content) as Record<string, string>;
};

const convertToLatex = async (proofTree: ConvertedProofTree, instructions: string = ""): Promise<Record<string, string>> => {
  const { stable, changing } = collectTexts(proofTree);
  return convertTextsToLatex([...stable, ...changing], instructions);
};

export { collectTexts, convertTextsToLatex };
export default convertToLatex;
