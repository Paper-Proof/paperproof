/**
 * in: `"h._@.Examples._hyg.1162"`  
 * out: `"h✝"`
 */
const prettifyHypothesisUsername = (username: string | null): string | null => {
  if (username === null) return null
  const prettyUsername = username.includes(".")
    ? `${username.split(".")[0]}✝`
    : username;
  return prettyUsername;
}

export default prettifyHypothesisUsername
