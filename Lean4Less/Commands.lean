import Lean
import Lean4Less.Replay
import Lean4Lean.Util
import Lean4Lean.Commands

open Lean
open Lean4Lean

def ppConst (env : Environment) (n : Name) : IO Unit := do
  let options := default
  let options := KVMap.set options `pp.proofs true
  let some info := env.find? n | unreachable!
  IO.print s!"{info.name}: {← (PrettyPrinter.ppExprLegacy env default default options info.type)}"

  match info.value? with
  | .some v => IO.println s!"\n{← (PrettyPrinter.ppExprLegacy env default default options v)}"
  | _ => IO.println ""

def transL4L (n : Name) : Lean.Elab.Command.CommandElabM Environment := do
  let (_, env) ← checkConstants (printErr := true) (← getEnv) (.insert default n) @Lean4Less.addDecl
  ppConst env n
  pure env

elab "#trans_l4l " i:ident : command => do
  _ ← transL4L i.getId

elab "#check_l4l " i:ident : command => do
  let env ← transL4L i.getId
  _ ← checkConstants (printErr := true) env (.insert default i.getId) @Lean4Lean.addDecl
  -- match macroRes with
  -- | some (name, _) => logInfo s!"Next step is a macro: {name.toString}"
  -- | none =>
  --   let kind := c.raw.getKind
  --   let elabs := commandElabAttribute.getEntries (←getEnv) kind
  --   match elabs with
  --   | [] => logInfo s!"There is no elaborators for your syntax, looks like its bad :("
  --   | _ => logInfo s!"Your syntax may be elaborated by: {elabs.map (fun el => el.declName.toString)}"
