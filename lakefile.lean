import Lake
open Lake DSL

-- TODO: this is an «examples» repo - the real «paperproof» library is in /lean subfolder.
-- We're only naming it "paperproof" here to accommodate to lean reservoir, see https://github.com/Paper-Proof/paperproof/pull/42.
-- Note that we're naming it lowercase paperproof to avoid circular dependency error.
-- In general, this should still be called «example», let's see how to deal with it when https://reservoir.lean-lang.org is more mature.
package «paperproof» {
  -- add package configuration options here
}

lean_lib «paperproof» {
  -- add library configuration options here
}

-- If you're developing locally, this imports paperproof from a local "./lean" folder
require Paperproof from "lean"

-- require Paperproof from git "https://github.com/Paper-Proof/paperproof.git"@"main"/"lean"

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.26.0-rc2"

-- Uncomment this is you want to use paperproof statically
-- @[default_target]
-- lean_exe terminal where
--   srcDir := "lean"
--   supportInterpreter := true
