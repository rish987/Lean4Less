import Lean4Less.Methods
import Lean4Less.Quot
import Lean4Less.Inductive.Add
import Lean4Less.Primitive
import Lean4Lean.Environment.Basic

namespace Lean4Less
namespace Kernel.Environment
open TypeChecker

open private Lean.Kernel.Environment.add from Lean.Environment
open Lean
open Lean.Kernel.Environment

structure LM.Context where
  lctx : LocalContext := {}
  -- lparams : List Name := []
  lparamsToFVars : Std.HashMap Name FVarId := {}

abbrev LM := ReaderT LM.Context Id

instance : MonadLCtx LM where
  getLCtx := return (← read).lctx

instance (priority := low) : MonadWithReaderOf LocalContext LM where
  withReader f := withReader fun s => { s with lctx := f s.lctx }

@[inline] def withLCtx [MonadWithReaderOf LocalContext m] (lctx : LocalContext) (x : m α) : m α :=
  withReader (fun _ => lctx) x

@[inline] def withLparamsToFVars [MonadWithReaderOf LM.Context m] (lparamsToFVars : Std.HashMap Name FVarId) (x : m α) : m α :=
  withReader (fun l => {l with lparamsToFVars}) x

def transL (params : List Name) (lamBind : Bool) (e : Expr) : LM Expr := do
  if params.length == 0 then return e
  let rec loop univNames lfvars lparamsToFVars := do 
    match univNames with
    | n::ns =>
      let name := n
      let id : FVarId := {name := `lvl_ ++ n}
      withLCtx ((← getLCtx).mkLocalDecl id name (Expr.const `L4L.Level []) .implicit) do
        let lparamsToFVars := lparamsToFVars.insert n id
        let lfvars := lfvars.push (Expr.fvar id)
        loop ns lfvars lparamsToFVars
    | [] => 
      withLparamsToFVars lparamsToFVars do
          let e ← sorry
          if lamBind then
            pure $ (← getLCtx).mkLambda lfvars e |>.toPExpr
          else
            pure $ (← getLCtx).mkForall lfvars e |>.toPExpr
  loop params #[] default

def _root_.Lean.Kernel.Environment.addWithLevels (env : Lean.Kernel.Environment) (ci : Lean.ConstantInfo) (elimUnivs : Bool) : Lean.Kernel.Environment := Id.run do
  if not elimUnivs then
    return env.add ci
  let lparams := ci.levelParams
  let type := ci.type
  let newType := transL lparams false type |>.run {}
  let newCi ← match ci with
    | .defnInfo     {value := v, ..}
    | .thmInfo      {value := v, ..}
    | .opaqueInfo   {value := v, ..} =>
      let newValue := transL lparams true v |>.run {}
      match ci with
        | .defnInfo   d => pure $ .defnInfo   {d with type := newType, value := newValue, levelParams := []}
        | .thmInfo    d => pure $ .thmInfo    {d with type := newType, value := newValue, levelParams := []}
        | .opaqueInfo d => pure $ .opaqueInfo {d with type := newType, value := newValue, levelParams := []}
        | _ => unreachable!
    | .axiomInfo    d => pure $ .axiomInfo  {d with type := newType, levelParams := []}
    | .quotInfo     d => pure $ .quotInfo   {d with type := newType, levelParams := []}
    | .inductInfo   d => pure $ .inductInfo {d with type := newType, levelParams := []}
    | .ctorInfo     d => pure $ .ctorInfo   {d with type := newType, levelParams := []}
    | .recInfo      d@{rules := rs, ..} => 
      let newRules := rs.map fun r => {r with rhs := transL lparams true r.rhs |>.run {}}
      pure $ .recInfo {d with type := newType, rules := newRules, levelParams := []}
  pure $ env.add newCi

def checkConstantVal (env : Kernel.Environment) (v : ConstantVal) (allowPrimitive := false) : M PExpr := do
  env.checkName v.name allowPrimitive
  checkDuplicatedUnivParams v.levelParams
  checkNoMVarNoFVar env v.name v.type
  let (typeType, type'?) ← check v.type v.levelParams
  let type' := type'?.getD v.type.toPExpr
  let (sort, typeTypeEqSort?) ← ensureSort typeType v.levelParams type'
  let type'' ← maybeCast typeTypeEqSort? typeType sort type' v.levelParams
  insertInitLets type''

def patchAxiom (env : Kernel.Environment) (v : AxiomVal) (opts : TypeCheckerOpts) :
    Except KernelException ConstantInfo := do
  let type ← (checkConstantVal env v.toConstantVal).run env v.name (opts := opts)
    (safety := if v.isUnsafe then .unsafe else .safe)
  if type.toExpr.hasFVar then
    throw $ .other "fvar in translated term"
  let v := {v with type}
  return .axiomInfo v

def patchDefinition (env : Kernel.Environment) (v : DefinitionVal) (allowAxiomReplace := false) (opts : TypeCheckerOpts) :
    Except KernelException ConstantInfo := do
  if let .unsafe := v.safety then
    -- Meta definition can be recursive.
    -- So, we check the header, add, and then type check the body.
    let type ← (checkConstantVal env v.toConstantVal).run env v.name (safety := .unsafe) (opts := opts)
    let env' := env.addWithLevels (.defnInfo {v with type}) opts.univs
    checkNoMVarNoFVar env' v.name v.value
    M.run env' v.name (safety := .unsafe) (lctx := {}) opts do
      let value ← do
        let (valueType, value'?) ← TypeChecker.check v.value v.levelParams
        let value' := value'?.getD v.value.toPExpr
        let (true, value) ← smartCast valueType type value' v.levelParams |
          -- if allowAxiomReplace then
          --   return .axiomInfo {v with type, isUnsafe := false}
          -- else
          throw <| .declTypeMismatch env' (.defnDecl v) valueType
        -- isValidApp value v.levelParams
        insertInitLets value
      if type.toExpr.hasFVar || value.toExpr.hasFVar then
        throw $ .other "fvar in translated term"
      let v := {v with type, value}
      return .defnInfo v
  else
    let type ← M.run env v.name (safety := .safe) (lctx := {}) opts do
      checkConstantVal env v.toConstantVal (← checkPrimitiveDef env v)
    checkNoMVarNoFVar env v.name v.value

    M.run env v.name (safety := .safe) (lctx := {}) opts do
      let value ← do
        -- dbg_trace s!"DBG[25]: Environment.lean:49: v.name={v.name}"
        -- dbg_trace s!"DBG[25]: Environment.lean:49: v.name={v.name}"
        -- dbg_trace s!"DBG[34]: Environment.lean:52 (after checkNoMVarNoFVar env v.name v.value)"
        let (valueType, value'?) ← TypeChecker.check v.value v.levelParams
        -- dbg_trace s!"DBG[98]: Environment.lean:54: valueType={valueType}"
        let value' := value'?.getD v.value.toPExpr
        -- dbg_trace s!"DBG[33]: Environment.lean:54 (after let value := value?.getD v.value.toPExpr)"
        -- dbg_trace s!"DBG[31]: Environment.lean:57: valueTypeEqtype?={valueTypeEqtype?}"

        let (true, value) ← smartCast valueType type value' v.levelParams |
          -- if allowAxiomReplace then
          --   return .axiomInfo {v with type, isUnsafe := false}
          -- else
          throw <| .declTypeMismatch env (.defnDecl v) valueType
        -- dbg_trace s!"DBG[0]: Methods.lean:202: patch={(Lean.collectFVars default type.toExpr).fvarIds.map fun v => v.name}"
        -- dbg_trace s!"DBG[1]: Methods.lean:202: patch={(Lean.collectFVars default value'.toExpr).fvarIds.map fun v => v.name}"
        -- dbg_trace s!"DBG[2]: Methods.lean:202: patch={(Lean.collectFVars default valueType.toExpr).fvarIds.map fun v => v.name}"
        -- dbg_trace s!"DBG[3]: Methods.lean:202: patch={← (Lean.collectFVars default value.toExpr).fvarIds.mapM fun v => do pure (v.name, (← get).fvarRegistry.get? v.name)}"
        -- dbg_trace s!"DBG[15]: Environment.lean:65 (after let value ← smartCast valueType type v…)"
        insertInitLets value
        -- isValidApp value v.levelParams
        -- dbg_trace s!"DBG[35]: Environment.lean:64 (after let v := v with type, value)"
      let v := {v with type, value}
      if type.toExpr.hasFVar || value.toExpr.hasFVar then
        throw $ .other "fvar in translated term"
      return (.defnInfo v)

def patchTheorem (env : Kernel.Environment) (v : TheoremVal) (allowAxiomReplace := false) (opts : TypeCheckerOpts) :
    Except KernelException ConstantInfo := do
  -- TODO(Leo): we must add support for handling tasks here
  let type ← M.run env v.name (safety := .safe) (lctx := {}) (opts := opts) do
    checkConstantVal env v.toConstantVal
  checkNoMVarNoFVar env v.name v.value

  M.run env v.name (safety := .safe) (lctx := {}) opts do
    let value ← do
      let (valueType, value'?) ← TypeChecker.check v.value v.levelParams
      let value' := value'?.getD v.value.toPExpr
      let (true, ret) ← smartCast valueType type value' v.levelParams |
        -- if allowAxiomReplace then
        --   pure none
        -- else
        throw <| .declTypeMismatch env (.thmDecl v) valueType
      insertInitLets ret
      -- isValidApp ret v.levelParams
    let v := {v with type, value}
    if type.toExpr.hasFVar || value.toExpr.hasFVar then
      throw $ .other "fvar in translated theorem type/value"
    return .thmInfo v
  -- if let .some value := value? then
  -- else
  --   let v := {v with type, isUnsafe := false}
  --   if type.toExpr.hasFVar then
  --     throw $ .other "fvar in translated axiom type"
  --   return .axiomInfo v

def patchOpaque (env : Kernel.Environment) (v : OpaqueVal) (opts : TypeCheckerOpts) :
    Except KernelException ConstantInfo := do
  let type ← M.run env v.name (safety := .safe) (lctx := {}) opts do
    checkConstantVal env v.toConstantVal
  M.run env v.name (safety := .safe) (lctx := {}) opts do
    let value ← do
      let (valueType, value'?) ← TypeChecker.check v.value v.levelParams
      let value' := value'?.getD v.value.toPExpr
      let (true, ret) ← smartCast valueType type value' v.levelParams |
        throw <| .declTypeMismatch env (.opaqueDecl v) valueType
      insertInitLets ret
    if type.toExpr.hasFVar || value.toExpr.hasFVar then
      throw $ .other "fvar in translated term"
    let v := {v with type, value}
    return .opaqueInfo v

def patchMutual (env : Kernel.Environment) (vs : List DefinitionVal) (opts : TypeCheckerOpts) :
    Except KernelException (List ConstantInfo) := do
  let v₀ :: _ := vs | throw <| .other "invalid empty mutual definition"
  if let .safe := v₀.safety then
    throw <| .other "invalid mutual definition, declaration is not tagged as unsafe/partial"
  let types ← M.run env `mutual (safety := v₀.safety) (lctx := {}) opts do
    let mut types := []
    for v in vs do
      if v.safety != v₀.safety then
        throw <| .other
          "invalid mutual definition, declarations must have the same safety annotation"
      let type ← checkConstantVal env v.toConstantVal
      types := types.append [type]
    pure types
  let mut env' := env
  let mut vs' := []
  for (type, v) in types.zip vs do
    let v' := {v with type}
    env' := env'.addWithLevels (.defnInfo v') opts.univs
    vs' := vs'.append [v']
  let mut newvs' := #[]
  for (v', type) in vs'.zip types do
    let newv' ← M.run env' `mutual (safety := v₀.safety) (lctx := {}) opts do
      let value ← do
        checkNoMVarNoFVar env' v'.name v'.value
        let (valueType, value'?) ← TypeChecker.check v'.value v'.levelParams
        let value' := value'?.getD v'.value.toPExpr
        let (true, value) ← smartCast valueType type value' vs[0]!.levelParams |
          throw <| .declTypeMismatch env' (.mutualDefnDecl vs') valueType
        insertInitLets value
      if type.toExpr.hasFVar || value.toExpr.hasFVar then
        throw $ .other "fvar in translated term"
      pure {v' with value}
    newvs' := newvs'.push newv'
  return newvs'.map .defnInfo |>.toList

/-- Type check given declaration and add it to the environment -/
def addDecl' (env : Kernel.Environment) (decl : @& Declaration) (opts : TypeCheckerOpts := {}) (allowAxiomReplace := false) :
    Except KernelException Kernel.Environment := do
  let add env ci := env.addWithLevels ci opts.univs
  match decl with
  | .axiomDecl v =>
    let v ← patchAxiom env v opts
    pure $ add env v
  | .defnDecl v =>
    let v ← patchDefinition env v allowAxiomReplace opts
    pure $ add env v
  | .thmDecl v =>
    let v ← patchTheorem env v allowAxiomReplace opts
    pure $ add env v
  | .opaqueDecl v =>
    let v ← patchOpaque env v opts
    pure $ add env v
  | .mutualDefnDecl vs =>
    let vs ← patchMutual env vs opts
    vs.foldlM (init := env) (fun env v => pure $ add env v)
  | .quotDecl =>
    addQuot env
  | .inductDecl lparams nparams types isUnsafe =>
    let allowPrimitive ← checkPrimitiveInductive env lparams nparams types isUnsafe opts
    addInductive add env lparams nparams types isUnsafe allowPrimitive -- TODO handle any possible patching in inductive type declarations (low priority)
