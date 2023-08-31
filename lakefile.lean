import Lake
open Lake DSL

package «examples» {
  -- add package configuration options here
}

lean_lib «Examples» {
  -- add library configuration options here
}

-- If you're developing locally, this imports paperproof from a local "./lean" folder
require Paperproof from "lean"

-- require Paperproof from git "https://github.com/Paper-Proof/paperproof.git"@"main"/"lean"

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"
