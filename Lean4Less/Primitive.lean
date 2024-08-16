import Lean4Less.TypeChecker

namespace Lean4Less
open Lean
open Lean4Less.TypeChecker

open private add from Lean.Environment

private def arrow := Expr.arrow

def checkPrimitiveDef (env : Environment) (v : DefinitionVal) : M Bool := do
  let fail {α} : M α := throw <| .other s!"invalid form for primitive def {v.name}"
  let nat := .const ``Nat []
  let bool := .const ``Bool []
  let tru := .const ``Bool.true []
  let fal := .const ``Bool.false []
  let zero := .const ``Nat.zero []
  let succ := mkApp (.const ``Nat.succ [])
  let pred := mkApp (.const ``Nat.pred [])
  let add := mkApp2 (.const ``Nat.add [])
  let mul := mkApp2 (.const ``Nat.mul [])
  let mod := mkApp2 (.const ``Nat.mod [])
  let defEq (a b : Expr) := TypeChecker.isDefEqPure a.toPExpr b.toPExpr v.levelParams
  let defeq1 (a b : Expr) := TypeChecker.isDefEqPure (arrow nat a).toPExpr (arrow nat b).toPExpr v.levelParams
  let defeq2 (a b : Expr) := defeq1 (arrow nat a).toPExpr (arrow nat b).toPExpr
  let x := .bvar 0
  let y := .bvar 1
  match v.name with
  | ``Nat.add =>
    unless env.contains ``Nat && v.levelParams.isEmpty do fail
    -- add : Nat → Nat → Nat
    unless ← TypeChecker.isDefEqPure v.type.toPExpr (arrow nat (arrow nat nat)).toPExpr v.levelParams do fail
    let add := mkApp2 v.value
    -- add x 0 ≡ x
    unless ← defeq1 (add x zero) x do fail
    -- add y (succ x) ≡ succ (add y x)
    unless ← defeq2 (add y (succ x)) (succ (add y x)) do fail
  | ``Nat.pred =>
    unless env.contains ``Nat && v.levelParams.isEmpty do fail
    -- pred : Nat → Nat
    unless ← defEq v.type (arrow nat nat) do fail
    let pred := mkApp v.value
    unless ← defEq (pred zero) zero do fail
    unless ← defeq1 (pred (succ x)) x do fail
  | ``Nat.sub =>
    unless env.contains ``Nat.pred && v.levelParams.isEmpty do fail
    -- sub : Nat → Nat → Nat
    unless ← defEq v.type (arrow nat (arrow nat nat)) do fail
    let sub := mkApp2 v.value
    unless ← defeq1 (sub x zero) x do fail
    unless ← defeq2 (sub y (succ x)) (pred (sub y x)) do fail
  | ``Nat.mul =>
    unless env.contains ``Nat.add && v.levelParams.isEmpty do fail
    -- mul : Nat → Nat → Nat
    unless ← defEq v.type (arrow nat (arrow nat nat)) do fail
    let mul := mkApp2 v.value
    unless ← defeq1 (mul x zero) zero do fail
    unless ← defeq2 (mul y (succ x)) (add (mul y x) y) do fail
  | ``Nat.pow =>
    unless env.contains ``Nat.mul && v.levelParams.isEmpty do fail
    -- pow : Nat → Nat → Nat
    unless ← defEq v.type (arrow nat (arrow nat nat)) do fail
    let pow := mkApp2 v.value
    unless ← defeq1 (pow x zero) (succ zero) do fail
    unless ← defeq2 (pow y (succ x)) (mul (pow y x) y) do fail
  | ``Nat.mod =>
    unless env.contains ``Nat.sub && v.levelParams.isEmpty do fail
    -- mod : Nat → Nat → Nat
    unless ← defEq v.type (arrow nat (arrow nat nat)) do fail
    let mod := mkApp2 v.value
    unless ← defeq1 (mod zero x) zero do fail
    return true -- TODO
  | ``Nat.div =>
    unless env.contains ``Nat.sub && v.levelParams.isEmpty do fail
    -- div : Nat → Nat → Nat
    unless ← defEq v.type (arrow nat (arrow nat nat)) do fail
    return true -- TODO
  | ``Nat.gcd =>
    unless env.contains ``Nat.mod && v.levelParams.isEmpty do fail
    -- gcd : Nat → Nat → Nat
    unless ← defEq v.type (arrow nat (arrow nat nat)) do fail
    let gcd := mkApp2 v.value
    unless ← defeq1 (gcd zero x) x do fail
    unless ← defeq2 (gcd (succ y) x) (gcd (mod x (succ y)) (succ y)) do fail
  | ``Nat.beq =>
    unless env.contains ``Nat && env.contains ``Bool && v.levelParams.isEmpty do fail
    -- beq : Nat → Nat → Bool
    unless ← defEq v.type (arrow nat (arrow nat bool)) do fail
    let beq := mkApp2 v.value
    unless ← defEq (beq zero zero) tru do fail
    unless ← defeq1 (beq zero (succ x)) fal do fail
    unless ← defeq1 (beq (succ x) zero) fal do fail
    unless ← defeq2 (beq (succ y) (succ x)) (beq y x) do fail
  | ``Nat.ble =>
    unless env.contains ``Nat && env.contains ``Bool && v.levelParams.isEmpty do fail
    -- ble : Nat → Nat → Bool
    unless ← defEq v.type (arrow nat (arrow nat bool)) do fail
    let ble := mkApp2 v.value
    unless ← defEq (ble zero zero) tru do fail
    unless ← defeq1 (ble zero (succ x)) tru do fail
    unless ← defeq1 (ble (succ x) zero) fal do fail
    unless ← defeq2 (ble (succ y) (succ x)) (ble y x) do fail
  | _ => return false
  return true

def checkPrimitiveInductive (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) : Except KernelException Bool := do
  unless !isUnsafe && lparams.isEmpty && nparams == 0 do return false
  let [type] := types | return false
  let defEq (a b : Expr) := TypeChecker.isDefEqPure a.toPExpr b.toPExpr lparams
  unless type.type == .sort (.succ .zero) do return false
  let fail {α} : Except KernelException α :=
    throw <| .other s!"invalid form for primitive inductive {type.name}"
  match type.name with
  | ``Bool =>
    let [⟨``Bool.false, .const ``Bool []⟩, ⟨``Bool.true, .const ``Bool []⟩] := type.ctors | fail
  | ``Nat =>
    let [
      ⟨``Nat.zero, .const ``Nat []⟩,
      ⟨``Nat.succ, .forallE _ (.const ``Nat []) (.const ``Nat []) _⟩
    ] := type.ctors | fail
  | ``String =>
    let [⟨``String.mk,
      .forallE _ (.app (.const ``List [.zero]) (.const ``Char [])) (.const ``String []) _
    ⟩] := type.ctors | fail
    M.run env (safety := .safe) (lctx := {}) (const := type.name) do
      -- We need the following definitions for `strLitToConstructor` to work:
      -- Nat : Type (this is primitive so checking for existence suffices)
      let nat := .const ``Nat []
      unless env.contains ``Nat do fail
      -- Char : Type
      let char := .const ``Char []
      _ ← TypeChecker.ensureType char.toPExpr lparams
      -- List Char : Type
      let listchar := mkApp (.const ``List [.zero]) char
      _ ← TypeChecker.ensureType listchar.toPExpr lparams
      -- @List.nil.{0} Char : List Char
      let listNil := .app (.const ``List.nil [.zero]) char
      unless ← defEq (← TypeChecker.checkPure listNil []) listchar do fail
      -- @List.cons.{0} Char : List Char
      let listCons := .app (.const ``List.cons [.zero]) char
      unless ← defEq (← TypeChecker.checkPure listCons [])
        (arrow char (arrow listchar listchar)) do fail
      -- String.mk : List Char → String (already checked)
      -- @Char.ofNat : Nat → Char
      let charOfNat := .const ``Char.ofNat []
      unless ← defEq (← TypeChecker.checkPure charOfNat []) (arrow nat char) do fail
  | _ => return false
  return true
