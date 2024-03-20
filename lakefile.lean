import Lake
open Lake DSL

package lean4lean

require std from git "https://github.com/leanprover/std4" @ "v4.7.0-rc2"

@[default_target]
lean_lib Lean4Lean

@[default_target]
lean_exe lean4lean where
  root := `Main
  supportInterpreter := true

@[default_target]
lean_lib Lean4Lean.Theory where
  globs := #[.andSubmodules `Lean4Lean.Theory]

@[default_target]
lean_lib Lean4Lean.Verify where
  globs := #[.andSubmodules `Lean4Lean.Verify]
