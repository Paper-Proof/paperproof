
/**
 * `"calc b ^ 3 + 1 = (2 * a) ^ 3 + 1 := by rw [h]"` => `"calc"`
 *
 * (see https://github.com/Paper-Proof/paperproof/issues/39)
 */
const prettifyTacticText = (text : string) => {
  if (text.startsWith('calc')) {
    return 'calc'
  } else {
    return text
  }
}

export default prettifyTacticText
