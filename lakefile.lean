import Lake
open Lake DSL

package lean4less

require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.26.0-rc2"

-- require lean4lean from "/home/rvaishna/projects/lean4lean/"

require lean4lean from git "https://github.com/rish987/lean4lean" @ "lean4less"

require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "v4.26.0-rc2"

@[default_target]
lean_lib patch { globs := #[Glob.submodules `patch] }

@[default_target]
lean_lib Lean4Less

@[default_target]
lean_exe lean4less where
  root := `Main
  supportInterpreter := true
