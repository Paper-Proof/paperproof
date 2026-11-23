import Lake
open System Lake DSL

package Paperproof

@[default_target]
lean_lib Paperproof where
  srcDir := if Lean.version.minor < 27 then "v4.25.0" else "v4.27.0"

lean_lib Tests
