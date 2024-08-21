// "a._@.Mathlib.Init.Algebra.Order._hyg.1764" => "a"
// (https://github.com/leanprover/lean4/blob/d37bbf4292c72798afdff8bf5488df09193fde58/src/Init/Prelude.lean#L4132)
// Note: I was doing this in the parser with `.eraseMacroScopes`, but we depend on hygienic goal usernames, might be dangerous - so I moved it here.
const prettifyGoalUsername = (username : string) => {
  return username.split('._@')[0];
}

export default prettifyGoalUsername
