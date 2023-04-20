import Lake
open System Lake DSL

package PaperProof

-- def yarnCmd: String := "yarn"

-- target packageLock : FilePath := do
--   let widgetDir := __dir__ / "widget"
--   let packageFile ← inputFile <| widgetDir / "package.json"
--   let packageLockFile := widgetDir / "yarn.lock"
--   buildFileAfterDep packageLockFile packageFile fun _srcFile => do
--     proc {
--       cmd := yarnCmd 
--       args := #["install"]
--       cwd := some widgetDir
--     }

-- open System Lake DSL
-- def tsxTarget (pkg : Package) (tsxName : String) [Fact (pkg.name = _package.name)]
--     : IndexBuildM (BuildJob FilePath) := do
--   let widgetDir := __dir__ / "widget"
--   let jsFile := widgetDir / "dist" / s!"{tsxName}.js"
--   let deps : Array (BuildJob FilePath) := #[
--     ← inputFile <| widgetDir / "src" / s!"{tsxName}.tsx",
--     ← inputFile <| widgetDir / "rollup.config.js",
--     ← inputFile <| widgetDir / "tsconfig.json",
--     ← fetch (pkg.target ``packageLock)
--   ]
--   buildFileAfterDepArray jsFile deps fun _srcFile => do
--     proc {
--       cmd := yarnCmd 
--       args := #["run", "build", "--tsxName", tsxName]
--       cwd := some widgetDir
--     }

-- target paperProofJs (pkg : Package) : FilePath := tsxTarget pkg "paperProof"

@[default_target]
lean_lib PaperProof

lean_lib Example
lean_lib Parser 

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"