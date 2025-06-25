import Lean.Structure
import Lean4Lean.Expr
import Lean4Less.EExpr
import Lean4Less.Ext
import Lean4Lean.Inductive.Reduce

namespace Lean4Less
open Lean
open Lean4Less.TypeChecker

section

variable [Monad m] [MonadReaderOf Context m] [MonadExcept KernelException M] (env : Kernel.Environment)
  (meth : ExtMethodsR m)

def getFirstCtor (dName : Name) : Option Name := do
  let some (.inductInfo info) := env.find? dName | none
  info.ctors.head?

def mkNullaryCtor (type : PExpr) (nparams : Nat) : Option (PExpr × Name) :=
  type.toExpr.withApp fun d args => do
  let .const dName ls := d | none
  let name ← getFirstCtor env dName
  return (mkAppRange (.const name ls) 0 nparams args |>.toPExpr, name)

/--
When `e` has the type of a K-like inductive, converts it into a constructor
application.

For instance if we have `e : Eq a a`, it is converted into `Eq.refl a` (which
it is definitionally equal to by proof irrelevance). Note that the indices of
`e`'s type must match those of the constructor application (for instance,
`e : Eq a b` cannot be converted if `a` and `b` are not defeq).
-/
def toCtorWhenK (rval : RecursorVal) (e : PExpr) : m (PExpr × Option (EExpr)) := do
  assert! rval.k
  let type ← meth.whnfPure 101 (← meth.inferTypePure 102 e)
  let .const typeI _ := type.toExpr.getAppFn | return (e, none)
  if typeI != rval.getMajorInduct then return (e, none)
  if type.toExpr.hasExprMVar then
    let typeArgs := type.toExpr.getAppArgs
    for h : i in [rval.numParams:typeArgs.size] do
      if (typeArgs[i]'h.2.1).hasExprMVar then return (e, none)
  let some (newCtorApp, newCtorName) := mkNullaryCtor env type rval.numParams | return (e, none)
  if let (.const ctorName _) := e.toExpr.getAppFn then
    if ctorName == newCtorName then
      if let true ← meth.isDefEqPure 103 e newCtorApp then
        return (e, none)
  let appType ← meth.inferTypePure 104 newCtorApp
  -- check that the indices of types of `e` and `newCtorApp` match
  let (true, pt?) ← meth.isDefEq 105 type appType | return (e, none)
  let prf? ←
    if (← readThe Context).opts.kLikeReduction || pt?.isSome then
      let elsecase := do
        let ret ← meth.isDefEqProofIrrel' e newCtorApp type appType pt?
        pure ret
      if let (.const ctorName _) := e.toExpr.getAppFn then
        if ctorName == newCtorName then
          pure none -- OK because of restrictions on the typing of K-like inductive constructors (i.e., ctor args must be indices)
        else
          elsecase -- should never actually happen since we're already WHNF, right?
      else
        -- TODO TODO TODO make sure that proof irrelevance is defined as a theorem if opts.proofIrrelevance = false
        elsecase
    else
      pure none

  return (newCtorApp, prf?)

def expandEtaStruct (eType e : PExpr) : m (PExpr × Option EExpr) :=
  eType.toExpr.withApp fun I args => do
    let .const I ls := I | return (e, none)
    let some ctor := getFirstCtor env I | return (e, none)
    let some (.ctorInfo info) := env.find? ctor | unreachable!
    let mut result := mkAppRange (.const ctor ls) 0 info.numParams args
    for i in [:info.numFields] do
      result := .app result (.proj I i e)
    let p? ←
      if (← readThe Context).opts.structLikeReduction then
        let .sort l := (← meth.whnfPure 0 (← meth.inferTypePure 0 eType)).toExpr | unreachable!
        let p : EExpr := .refl {u := l, A := eType, a := e}
        pure $ .some p
      else pure none
    pure (result.toPExpr, p?)

/--
When `e` is of struct type, converts it into a constructor application using
projections.

For instance if we have `e : String`, it is converted into
`String.mk (String.data e)` (which is definitionally equal to `e` by struct
eta).
-/
def toCtorWhenStruct (inductName : Name) (e : PExpr) : m (PExpr × Option EExpr) := do
  if !isStructureLike' env inductName || (isConstructorApp?' env e.toExpr).isSome then
    return (e, none)
  let eType ← meth.whnfPure 107 (← meth.inferTypePure 106 e)
  if !eType.toExpr.getAppFn.isConstOf inductName then return (e, none)
  if (← meth.whnfPure 108 (← meth.inferTypePure 109 eType)).toExpr == Expr.prop then return (e, none)
  expandEtaStruct env meth eType e

def getRecRuleFor (rval : RecursorVal) (major : Expr) : Option RecursorRule := do
  let .const fn _ := major.getAppFn | none
  rval.rules.find? (·.ctor == fn)

/--
Performs recursor reduction on `e` (returning `none` if not applicable).

For recursor reduction to occur, `e` must be a recursor application where the
major premise is either a complete constructor application or of a K- or
structure-like inductive type (in which case it is converted into an equivalent
constructor application). The reduction is done by applying the
`RecursorRule.rhs` associated with the constructor to the parameters from the
recursor application and the fields of the constructor application.
-/
def inductiveReduceRec [Monad m] [MonadLCtx m] [MonadExcept KernelException m] [MonadWithReaderOf (Std.HashMap (FVarId × FVarId) FVarDataE) m] (env : Kernel.Environment) (e : PExpr) (cheapK : Bool := false)
    : m (Option (PExpr × Option EExpr)) := do
  let recFn := e.toExpr.getAppFn
  let .const recFnName ls := recFn | return none
  let some (.recInfo info) := env.find? recFnName |
    return none
  let recType := info.type.instantiateLevelParams info.levelParams ls
  let recArgs := e.toExpr.getAppArgs
  let majorIdx := info.getMajorIdx
  let some major' := recArgs[majorIdx]? | return none
  let major := major'.toPExpr
  let (majorWhnf, majorEqmajorWhnf?) ← if info.k then pure (← meth.whnfPure 0 major, none) else meth.whnf 110 major
  let (majorKWhnf, majorWhnfEqmajorKWhnf?) ← if info.k && not cheapK then toCtorWhenK env meth info majorWhnf else pure (majorWhnf, none)
  let majorEqmajorKWhnf? ← meth.appHEqTrans? major majorWhnf majorKWhnf majorEqmajorWhnf? majorWhnfEqmajorKWhnf?
  let (majorMaybeCtor, majorKWhnfEqMajorMaybeCtor?) ← match majorKWhnf.toExpr with
    | .lit l => pure (l.toConstructor.toPExpr, none)
    | _ => toCtorWhenStruct env meth info.getMajorInduct majorKWhnf
  let majorEqMajorMaybeCtor? ← meth.appHEqTrans? major majorKWhnf majorMaybeCtor majorEqmajorKWhnf? majorKWhnfEqMajorMaybeCtor?
  -- (majorIdx, majorEqMajorMaybeCtor?)
  let some rule := getRecRuleFor info majorMaybeCtor | return none
  let majorArgs := majorMaybeCtor.toExpr.getAppArgs
  if rule.nfields > majorArgs.size then return none
  if ls.length != info.levelParams.length then return none
  let mut rhs := rule.rhs.instantiateLevelParams info.levelParams ls
  let getNestedType (t' : PExpr) := do
    let t? := t'.toExpr.find? fun
        | e@(.app ..) => 
          let fn := e.getAppFn
          if let .const n .. := fn then
             info.all.any (· == n)
          else
            false
        | .const n .. => info.all.any (· == n)
        | _ => false
    pure t?.get!

  let type ← getNestedType $ ← meth.whnfPure 111 $ ← meth.inferTypePure 112 major
  let newType ← getNestedType $ ← meth.whnfPure 112 (← meth.inferTypePure 113 majorMaybeCtor)
  let typeArgs := type.getAppArgs
  let newTypeArgs := newType.getAppArgs
  let mut argEqs? : Array (Option EExpr) := #[]
  for (arg, newArg) in typeArgs.zip newTypeArgs do
    let (arg, newArg) := (arg.toPExpr, newArg.toPExpr)
    let (true, p?) ← meth.isDefEq 136 arg newArg | panic! ""
    argEqs? := argEqs?.push p?

  let (paramEqs?, indEqs?) ←
      pure (argEqs?[:info.numParams].toArray, argEqs?[info.numParams:].toArray)

  let (params, _indices) ←
      pure (typeArgs[:info.numParams].toArray, typeArgs[info.numParams:].toArray)
  let (newParams, newIndices) ←
      pure (newTypeArgs[:info.numParams].toArray, newTypeArgs[info.numParams:].toArray)

  let numMotivesMinors := info.numMotives + info.numMinors
  let motivesMinors? ← do
    if paramEqs?.any (·.isSome) then
      pure $ some (← replaceParams meth recType params newParams recArgs[info.numParams:info.numParams + numMotivesMinors])
    else
      pure none

  let mut newRecArgs := recArgs.set! majorIdx majorMaybeCtor
  let mut map : Std.HashMap Nat (Option EExpr) := .insert default majorIdx majorEqMajorMaybeCtor?

  for idx in [:paramEqs?.size] do
    let paramEq? := paramEqs?[idx]!
    map := map.insert idx paramEq?
    newRecArgs := newRecArgs.set! idx newParams[idx]!

  let motivesStartIdx := info.numParams
  if let some motivesMinors := motivesMinors? then
    for idx in [:numMotivesMinors] do
      let (newMotiveMinor, p?) := motivesMinors[idx]!
      let recIdx := motivesStartIdx + idx
      map := map.insert recIdx p?
      newRecArgs := newRecArgs.set! recIdx newMotiveMinor
  else
    for idx in [:numMotivesMinors] do
      let recIdx := motivesStartIdx + idx
      map := map.insert recIdx .none

  let indicesStartIdx := info.numParams + numMotivesMinors
  for idx in [:indEqs?.size] do
    let indEq? := indEqs?[idx]!
    let recIdx := indicesStartIdx + idx
    map := map.insert recIdx indEq?
    newRecArgs := newRecArgs.set! recIdx newIndices[idx]!

  -- try
  --   _ ← meth.inferTypePure 10001 eNewMajor'
  -- let (_, eNewMajor?) := (← meth.inferType 121 eNewMajor') -- cast remaining args as necessary
  -- let eNewMajor := eNewMajor?.getD eNewMajor'

  -- get parameters from recursor application (recursor rules don't need the indices,
  -- as these are determined by the constructor and its parameters/fields)
  rhs := mkAppRange rhs 0 info.getFirstIndexIdx newRecArgs
  -- get fields from constructor application
  rhs := mkAppRange rhs (majorArgs.size - rule.nfields) majorArgs.size majorArgs

  if map.values.any (·.isSome) then
    let remArgs := recArgs[majorIdx + 1:].toArray
    let eNewMajor' := mkAppN recFn newRecArgs[:majorIdx + 1] |>.toPExpr
    let eNewMajorType' := (← meth.inferTypePure 121 eNewMajor')
    let e' := (mkAppN recFn recArgs[:majorIdx + 1]) |>.toPExpr
    let eType' := (← meth.inferTypePure 129 e')
    -- dbg_trace s!"DBG[3]: Reduce.lean:198 (after let eType := (← meth.inferTypeLean 129…) {← meth.getTrace true}"
    -- _ ← meth.inferTypeCheck eNewMajor'
    -- dbg_trace s!"DBG[2]: Reduce.lean:198 (after let eNewMajorType := (← meth.inferType…)"
    let remArgsData ← replaceFType meth eType' eNewMajorType' remArgs
    let remArgsNew := remArgsData.map fun (remArgNew, _) => remArgNew
    let remArgsNewEqRemArgs? := remArgsData.map fun (_, remArgNewEqremArg?) => remArgNewEqremArg?
    let mut idx := majorIdx + 1
    for remArgNewEqRemArg? in remArgsNewEqRemArgs? do
      map := map.insert idx remArgNewEqRemArg?
      idx := idx + 1

    let eNewMajor := Lean.mkAppN eNewMajor' remArgsNew |>.toPExpr
    let newe := Lean.mkAppN rhs remArgsNew |>.toPExpr
    -- _ ← meth.inferTypePure 7000 newe.toPExpr -- sanity check TODO remove
    let (.true, eEqeNewMajor?) ← meth.isDefEqApp 2 e eNewMajor map | unreachable!

    return .some (newe, eEqeNewMajor?)
  else
    let newe := mkAppRange rhs (majorIdx + 1) recArgs.size recArgs |>.toPExpr
    return .some (newe, none)

end
