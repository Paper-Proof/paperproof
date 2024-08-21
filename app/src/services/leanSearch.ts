import { Client } from "@gradio/client";
import { PredictReturn } from "@gradio/client/dist/types";

function decodeUnicode(str: string): string {
  return JSON.parse(`"${str}"`);
}

const extractFormalStatements = (input: string): string[] => {
  const parser = new DOMParser();
  const doc = parser.parseFromString(input, 'text/html');
  return Array.from(doc.querySelectorAll('td:nth-child(2)'))
    .map((el) => el.textContent?.trim() || '')
    .filter(Boolean)
    .map(decodeUnicode);
}

// Finds stuff in https://leansearch.net
// leanSearch("from: ¬∃ x, x ∈ Aᶜ, to: ∀ (x : X), x ∉ Aᶜ")
const leanSearch = async (searchString: string): Promise<string[]> => {
  const client = await Client.connect("https://css-app-ltlnq2swupkhgfoq-leanseek.scitix.ai/");
  
  const result: PredictReturn = await client.predict("/search_1", {
    query: searchString,
    num_results: 5,
  });

  if (Array.isArray(result.data) && result.data[0]) {
    const htmlPage = result.data[0]
    const arrayOfTheorems = extractFormalStatements(htmlPage)
    const arrayOfTheoremsWithPrettyUnicodeSymbols = arrayOfTheorems.map(decodeUnicode)
    return arrayOfTheoremsWithPrettyUnicodeSymbols
  } else {
    return []
  }
}

export default leanSearch;
