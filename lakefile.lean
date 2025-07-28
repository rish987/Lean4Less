import Lake
open Lake DSL

package lean4less

require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.21.0-rc3"

require lean4lean from "/home/rish/lean4lean/"

-- require lean4lean from git "https://github.com/rish987/lean4lean" @ "lean4less"

require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "main"

@[default_target]
lean_lib patch { globs := #[Glob.submodules `patch] }

@[default_target]
lean_lib Lean4Less

@[default_target]
lean_exe lean4less where
  root := `Main
  supportInterpreter := true
