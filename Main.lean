/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.CoreM
import Cli
import Lean.Util.FoldConsts
import Lean4Less.Environment
import Lean4Less.Fixtures.Tests -- FIXME should use separate fixtures dir
import Lean4Less.Replay
import Lean4Less.Commands

open Lean
open Lean4Lean
open Cli

open private add from Lean.Environment

def outDir : System.FilePath := System.mkFilePath [".", "out"]

/--
Run as e.g. `lake exe lean4lean` to check everything on the Lean search path,
or `lake exe lean4lean Mathlib.Data.Nat.Basic` to check a single file.

This will replay all the new declarations from the target file into the `Environment`
as it was at the beginning of the file, using the kernel to check them.

You can also use `lake exe lean4lean --fresh Mathlib.Data.Nat.Basic` to replay all the constants
(both imported and defined in that file) into a fresh environment.
-/
unsafe def runTransCmd (p : Parsed) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mod : Name := p.positionalArg! "input" |>.value.toName
  let onlyConsts? := p.flag? "only" |>.map fun onlys => 
    onlys.as! (Array String)
  match mod with
    | .anonymous => throw <| IO.userError s!"Could not resolve module: {mod}"
    | m =>
      let (lemmEnv, success) ← Lean.Elab.runFrontend (include_str "patch" / "PatchTheoremsAx.lean") default default `Patch
      if not success then
        throw $ IO.userError $ "elab of patching defs failed"
      if let some onlyConsts := onlyConsts? then
        Lean.withImportModules #[{module := mod}] {} 0 fun env => do
          let mut env := env
          for (_, c) in lemmEnv.constants do
            env := add env c
          _ ← Lean4Less.checkL4L (onlyConsts.map (·.toName)) env (printProgress := true)
      else
        replayFromInit' Lean4Less.addDecl m lemmEnv (op := "patch") (erase := false) (initConsts? := Lean4Less.patchConsts) fun env' =>
          replayFromEnv Lean4Lean.addDecl m env' (op := "typecheck") (opts := {proofIrrelevance := false, kLikeReduction := false})
  return 0

unsafe def transCmd : Cmd := `[Cli|
  transCmd VIA runTransCmd; ["0.0.1"]
  "Translate from Lean to Lean-."

  FLAGS:
    -- p, print;               "Print translation of specified constants to standard output (relevant only with '-o ...')."
    -- w, write;               "Also write translation of specified constants (with dependencies) to file (relevant only with '-p')."
    o, only : Array String; "Only translate the specified constants and their dependencies."
    a, appopt : Bool; "Optimize application case"

  ARGS:
    input : String;         "Input .lean file."

  -- The EXTENSIONS section denotes features that
  -- were added as an external extension to the library.
  -- `./Cli/Extensions.lean` provides some commonly useful examples.
  EXTENSIONS:
    author "rish987"
]

unsafe def main (args : List String) : IO UInt32 := do
  transCmd.validate args
