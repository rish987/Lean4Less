/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.CoreM
import Lean.Util.FoldConsts
import Lean4Less.Environment
import Lean4Less.Replay

open Lean
open Lean4Lean

def outDir : System.FilePath := System.mkFilePath [".", "out"]

/--
Run as e.g. `lake exe lean4lean` to check everything on the Lean search path,
or `lake exe lean4lean Mathlib.Data.Nat.Basic` to check a single file.

This will replay all the new declarations from the target file into the `Environment`
as it was at the beginning of the file, using the kernel to check them.

You can also use `lake exe lean4lean --fresh Mathlib.Data.Nat.Basic` to replay all the constants
(both imported and defined in that file) into a fresh environment.
-/
unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let (flags, args) := args.partition fun s => s.startsWith "--"
  let verbose : Bool := "--verbose" ∈ flags
  match args with
    | [mod] => match mod.toName with
      | .anonymous => throw <| IO.userError s!"Could not resolve module: {mod}"
      | m =>
          replayFromFresh Lean4Less.addDecl m verbose false
    | _ => do
      throw <| IO.userError "TODO not implemented"
      -- let sp ← searchPathRef.get
      -- let sp := [sp[0]!] -- FIXME
      -- let mut tasks : Array (Name × Task (Except IO.Error Unit)) := #[]
      -- for path in (← SearchPath.findAllWithExt sp "olean") do
      --   dbg_trace s!"DBG[2]: Main.lean:44: m={path}"
      --   if let some m ← searchModuleNameOfFileName path sp then
      --     replayFromImports m verbose compare
      -- for (m, t) in tasks do
      --   if let .error e := t.get then
      --     IO.eprintln s!"lean4lean found a problem in {m}"
      --     throw e
  return 0
