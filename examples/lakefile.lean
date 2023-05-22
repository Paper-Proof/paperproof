import Lake
open Lake DSL

package «examples» {
  -- add package configuration options here
}

lean_lib «Examples» {
  -- add library configuration options here
}

require PaperProof from ".."/"lean"
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"