/**
 * Finds all positions where a substring exists as a complete word (not part of a larger identifier) in text.
 * 
 * ___Why not use a usual \b word boundary check?
 *    Because we need to support Unicode characters, e.g. "hfiₗ".
 * 
 * @param text - The text to search in
 * @param substring - The word to find as a standalone term
 * @returns Array of start positions where substring exists as a separate word
 * 
 * @example
 * ("apply xₗ y₀", "xₗ")                       //=> [6] (found at position 6)
 * ("M.LeftTU.apply_left x", "apply")          //=> [] (part of apply_left)
 * ("M.LeftTU.comp_rows Sum.apply x", "apply") //=> [21] (found at position 21)
 * ("apply and apply again", "apply")          //=> [0, 10] (found at both positions)
 */
const findAllMatches = (text: string, substring: string): number[] => {
  const positions: number[] = [];
  let index = 0;
  
  while ((index = text.indexOf(substring, index)) !== -1) {
    const prevChar = index > 0 ? text[index - 1] : ' ';
    const nextChar = index + substring.length < text.length ? text[index + substring.length] : ' ';
    
    // All characters that Lean var name can have (according to Claude)
    const letterRegex = /[\p{L}\p{Nl}\p{Mn}\p{Mc}\p{Nd}\p{Pc}_'!?]/u;
    const isWordBoundary = !letterRegex.test(prevChar) && !letterRegex.test(nextChar);

    if (isWordBoundary) {
      positions.push(index);
    }

    index += 1;
  }
  
  return positions;
};

export interface SubstringMatch<T = any> {
  start: number;
  end: number;
  item: T;
}

/**
 * Finds all substring matches in text that exist as complete words (with word boundaries).
 */
const findSubstringMatches = <T>(text: string, items: T[], getItemString: (item: T) => string): SubstringMatch<T>[] => {
  return items
    .flatMap(item => {
      const searchString = getItemString(item);
      const positions = findAllMatches(text, searchString);

      return positions.map(start => ({ start, end: start + searchString.length, item }));
    })
    .sort((a, b) => a.start - b.start);
};

/**
 * Renders text with highlighted matches, using a custom render function for matched items.
 */
const renderTextWithMatches = <T>(
  text: string,
  items: T[],
  getItemString: (item: T) => string,
  renderMatch: (match: SubstringMatch<T>, index: number, text: string) => React.ReactNode
): (string | React.ReactNode)[] => {
  const matches = findSubstringMatches(text, items, getItemString);
  
  if (matches.length === 0) {
    return [text];
  }
  
  const parts: (string | React.ReactNode)[] = [];
  let lastIndex = 0;
  
  matches.forEach((match, index) => {
    // Add text before the match
    if (match.start > lastIndex) {
      parts.push(text.substring(lastIndex, match.start));
    }

    // Add the rendered match
    parts.push(renderMatch(match, index, text));
    
    lastIndex = match.end;
  });

  // Add remaining text
  if (lastIndex < text.length) {
    parts.push(text.substring(lastIndex));
  }
  
  return parts;
};

export default {
  findAllMatches,
  findSubstringMatches,
  renderTextWithMatches
}
