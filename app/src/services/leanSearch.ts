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
const leanSearch = async (searchString: string) : Promise<string[]> => {
  const response = await fetch('https://css-app-ltlnq2swupkhgfoq-leanseek.scitix.ai/call/search_1', {
    method: 'POST',
    headers: { 
      'Content-Type': 'application/json',
      'Accept': 'application/json'
    },
    body: JSON.stringify({
      data: [
        searchString,
        5
      ]
    })
  });

  const { event_id } = await response.json();
  const eventStream = await fetch(`https://css-app-ltlnq2swupkhgfoq-leanseek.scitix.ai/call/search_1/${event_id}`);

  const reader = eventStream.body?.getReader();
  let all = ''
  while (reader) {
    const { done, value } = await reader.read();
    if (done) break;
    const response = new TextDecoder().decode(value);
    all += response
  }
  return extractFormalStatements(all);
}

export default leanSearch;
