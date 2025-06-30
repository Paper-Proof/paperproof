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
 * 
 */
const findAllWordBoundaryMatches = (text: string, substring: string): number[] => {
  const positions: number[] = [];
  let index = 0;
  
  while ((index = text.indexOf(substring, index)) !== -1) {
    const prevChar = index > 0 ? text[index - 1] : ' ';
    const nextChar = index + substring.length < text.length ? text[index + substring.length] : ' ';
    const isWordBoundary = !/[a-zA-Z0-9_]/.test(prevChar) && !/[a-zA-Z0-9_]/.test(nextChar);
    
    if (isWordBoundary) {
      positions.push(index);
    }
    
    index += 1;
  }

  return positions;
};

export default findAllWordBoundaryMatches;
