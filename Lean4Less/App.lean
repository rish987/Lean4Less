import Lean.Structure
import Lean4Lean.Expr
import Lean4Less.EExpr
import Lean4Less.Ext

import Init.Data.List.Nat.Basic
import Init.Data.Array.Mem
import Init.Data.Array.DecidableEq
import Init.Data.Range.Lemmas
import Init.Data.List.ToArray
import Init.Data.List.Control
import Init.Data.Array.Basic
import Init.Data.Array.Bootstrap

-- 241
-- mkId 218

open Lean

section
namespace Lean4Less.TypeChecker.Inner

structure ExtMethodsA (m : Type → Type u) extends ExtMethods m where
  isDefEqForall (t s : PExpr) (numBinds : Nat) (f : Option EExpr → m (Option T)) : m (Bool × Option T)
  -- alignForAll (numBinds : Nat) (ltl ltr : Expr) : m (Expr × Expr)
  opt : Bool := true

variable [Monad m] [MonadLCtx m] [MonadExcept Kernel.Exception m] [MonadNameGenerator m] [MonadWithReaderOf LocalContext m] [MonadWithReaderOf (Std.HashMap (FVarId × FVarId) FVarDataE) m] (env : Environment) -- TODO more central place to declare these?
  (meth : ExtMethodsA m)

namespace App

def mkAppEqProof? (aVars bVars : Array LocalDecl) (us vs : Array Level) (Uas Vbs : Array PExpr) (UasEqVbs? : Array (Option EExpr))(ds? : Array (Option (LocalDecl × LocalDecl × EExpr))) (as bs : Array PExpr) (asEqbs? : Array (Option EExpr)) (f g : PExpr) (usedLets' : FVarIdSet) (fEqg? : Option EExpr := none)
: m (Option EExpr) := do
  let mut fEqg? := fEqg?
  let mut f := f
  let mut g := g
  for idx in [:as.size] do
    let a := as[idx]!
    let b := bs[idx]!
    let aEqb? := asEqbs?[idx]!

    fEqg? ←
      if aEqb?.isSome || fEqg?.isSome then
        let aVar := aVars[idx]!
        let bVar := bVars[idx]!
        let u := us[idx]!
        let v := vs[idx]!
        let d? := ds?[idx]!
        let A := aVar.type.toPExpr

        let Ua := Uas[idx]!
        let Vb := Vbs[idx]!

        let UaEqVb? := UasEqVbs?[idx]!

        let (U, V) := ((Ua, aVar), (Vb, bVar))

        let elseCase := do
          let elseCase' := do -- TODO FIXME only needed because I can't combine the conditions below
            if let some fEqg := fEqg? then
              if let some aEqb := aEqb? then
                pure $ .none {g, fEqg, b, aEqb}
              else
                pure $ .Fun {g, fEqg}
            else
              if let some aEqb := aEqb? then
                pure $ .Arg {b, aEqb}
              else
                unreachable!
          if let .some UaEqVb := UaEqVb? then
            if let some fEqg := fEqg? then
              let hUV := {a := aVar, UaEqVb, extra := .none, alets := ← meth.getLets 4 aVar}
              if let some aEqb := aEqb? then
                pure $ .UV {V, hUV, g, fEqg, b, aEqb}
              else
                pure $ .UVFun {V, hUV, g, fEqg}
            else
              -- let defEq ← meth.isDefEqPure 241 Ua Vb --sanity check
              -- assert! defEq
              elseCase'
          else
            elseCase'

        let extra ← if let .some (vaEqb, vbEqa, hAB) := d? then
          let B := bVar.type.toPExpr

          let some fEqg := fEqg? | do
            assert! (← meth.isDefEqPure 55501 A B)
            elseCase
          let some aEqb := aEqb? |
            assert! (← meth.isDefEqPure 55502 A B)
            elseCase

          -- Ua and Vb may still contain references to a and b despite being
          -- defeq (if dep == true), so we need to consider this case, and
          -- cannot immediately fall back to .AB (which has no dependent variant)
          let dep := Ua.containsFVar' aVar || Vb.containsFVar' bVar

          if UaEqVb?.isSome || dep then
            let UaEqVb ← UaEqVb?.getDM $ meth.mkHRefl 200 v.succ (Expr.sort v).toPExpr Ua
            let hUV := {a := aVar, UaEqVb, extra := .some {b := bVar, vaEqb := {aEqb := vaEqb, bEqa := vbEqa, lets := ← meth.getLets 5 vaEqb}, blets := ← meth.getLets 6 bVar}, alets := ← meth.getLets 7 aVar}
            let ret := .ABUV {B, hAB, V, hUV, g, fEqg, b, aEqb}
            pure ret
          else
            assert! not dep
            pure $ .AB {B, hAB, g, fEqg, b, aEqb}
        else
          elseCase
        pure $ .some $ .app {u, v, A, U, f, a, extra, usedLets'}
      else
        pure none
    f := f.toExpr.app a |>.toPExpr
    g := g.toExpr.app b |>.toPExpr
  pure fEqg?

def mkAppEqProof (TLam SLam : PExpr) (TVarLams SVarLams : Array ((Array Nat) × Name × BinderInfo × PExpr)) (TEqS? : Option EExpr) (as bs : Array PExpr) (asEqbs? : Array (Option EExpr)) (f g : PExpr) (usedLets' : FVarIdSet) (fEqg? : Option EExpr := none) : m (Option EExpr) := do
  let rec loop (idx : Nat) aVars bVars Uas Vbs UasEqVbs? ds? us vs : m (Option EExpr) := do
    -- try
    --   let fType ← meth.inferTypePure 2071 (Lean.mkAppN f.toExpr (as[:idx].toArray.map (·.toExpr))).toPExpr -- sanity check TODO remove
    --   let .true ← meth.isDefEqPure 209 T fType | do
    --     -- throw $ .other s!"expected 3 ({idx}): {T}\n inferred: {fType}\n f: {f}"
    --     throw $ .other s!"expected 3 ({idx})"
    -- catch e =>
    --   throw e

    -- let (T', dA, S', dB) ← match (← meth.whnfPure 205 T).toExpr, (← meth.whnfPure 206 S).toExpr with
    --   | .forallE tName tDom tBody tBi, .forallE sName sDom sBody sBi =>
    --     pure $ (tBody, ({name := tName, dom := tDom.toPExpr, info := tBi} : BinderData), sBody, ({name := sName, dom := sDom.toPExpr, info := sBi} : BinderData))
    --   | tBody, sBody => unreachable!


    let (aIdxs, aName, aBi, ALam) := TVarLams[idx]!
    let A := Lean.mkAppN ALam (aIdxs.map (fun idx => as[idx]!.toExpr)) |>.toPExpr

    let (bIdxs, bName, bBi, BLam) := SVarLams[idx]!
    let B := Lean.mkAppN BLam (bIdxs.map (fun idx => bs[idx]!.toExpr)) |>.toPExpr

    -- let ({name := aName, dom := A, info := aBi},
    --   {name := bName, dom := B, info := bBi}) := (dA, dB)

    -- sanity check
    -- let aType ← meth.inferTypePure 207 a
    -- let bType ← meth.inferTypePure 208 b
    -- let .true ← meth.isDefEqPure 209 A aType | do
    --   -- throw $ .other s!"expected 1: {A}\n inferred: {aType}\n a: {a}"
    --   throw $ .other s!"failed sanity check 1"
    -- let .true ← meth.isDefEqPure 210 B bType | do
    --   -- let app := Lean.mkAppN g.toExpr (bs[:5].toArray.map PExpr.toExpr)
    --   -- let appType ← meth.whnfPure $ ← meth.inferTypePure app.toPExpr 205
    --   -- let .forallE _ _domType _ _ := appType.toExpr | unreachable!
    --   -- meth.trace s!""
    --   -- meth.trace s!"app: {appType}"
    --   -- meth.trace s!"b: {bType}"
    --   -- meth.trace s!"dom: {domType}"
    --   -- meth.trace s!"eq: {← isDefEqPure bType domType.toPExpr}"
    --   -- meth.trace s!"app b: {← whnfPure $ ← inferTypePure (app.app b).toPExpr}"
    --   -- meth.trace s!""
    --   -- throw $ .other s!"expected 2: {B}\n inferred: {bType}"
    --   throw $ .other s!"failed sanity check 2"

    let AEqB? ←
      if A != B then
        let (defEq, AEqB?) ← meth.isDefEq 211 A B
        assert! defEq
        if AEqB?.isSome then
          if asEqbs?[idx]!.isSome then
            -- if idx == 0 then
            pure AEqB?
          else
            -- assert! ← meth.isDefEqPure 212 A B
            pure none
        else
          pure none
      else pure none

    let sort ← meth.inferTypePure 213 A
    let .sort u := (← meth.ensureSortCorePure sort A).toExpr | throw $ .other "unreachable 5"
    meth.withNewFVar 201 aName A aBi fun aVar => do
      let cont d? bVar := do 
        let ds? := ds?.push d?

        let TLamInitArgs := as[:idx].toArray.push aVar.toExpr.toPExpr
        let SLamInitArgs := bs[:idx].toArray.push bVar.toExpr.toPExpr

        let m := fun (decls, prevArgs) (idxs, n, bi, lam) => do
          let lamArgs := idxs.map (fun idx => prevArgs[idx]!.toExpr)
          let type := Lean.mkAppN lam lamArgs
          let decl := .cdecl 0 (.mk (← meth.mkId 220 type)) n type bi default
          pure (decls.push decl, prevArgs.push decl.toExpr.toPExpr)
        let TVars : Array LocalDecl := Prod.fst $ ← (TVarLams[idx + 1:]).foldlM (init := (#[], TLamInitArgs)) m
        let SVars : Array LocalDecl := Prod.fst $ ← (SVarLams[idx + 1:]).foldlM (init := (#[], SLamInitArgs)) m

        let TLCtx := TVars.foldl (init := (← getLCtx)) fun lctx decl => lctx.addDecl decl
        let SLCtx := SVars.foldl (init := (← getLCtx)) fun lctx decl => lctx.addDecl decl

        let TLamArgs := TLamInitArgs ++ (TVars.map fun v => v.toExpr.toPExpr)
        let SLamArgs := SLamInitArgs ++ (SVars.map fun v => v.toExpr.toPExpr)

        let Ua := TLCtx.mkForall (TVars.map (·.toExpr)) (Lean.mkAppN TLam (TLamArgs.map (·.toExpr))) |>.toPExpr
        let Vb := SLCtx.mkForall (SVars.map (·.toExpr)) (Lean.mkAppN SLam (SLamArgs.map (·.toExpr))) |>.toPExpr
        assert! (← meth.isDefEqLean Ua Vb)

        let sort ← meth.inferTypePure 238 Ua
        let .sort v := (← meth.ensureSortCorePure sort A).toExpr | throw $ .other "unreachable 5"

        let us := us.push u
        let vs := vs.push v

        let aVars := aVars.push aVar
        let bVars := bVars.push bVar
        let Uas := Uas.push Ua
        let Vbs := Vbs.push Vb
        let (true, UaEqVb?) ← meth.isDefEq 202 Ua Vb | throw $ .other "hUV error in isDefEqApp"
        -- let dep := Ua.containsFVar' aVar || Vb.containsFVar' bVar
        -- let UaEqVb? := if d?.isSome && dep then .some $ .sry {u := v.succ, A := (Expr.sort v).toPExpr, B := (Expr.sort v).toPExpr, a := Ua, b := Vb} else none
        -- let UaEqVb? := .some $ .sry {u := v.succ, A := (Expr.sort v).toPExpr, B := (Expr.sort v).toPExpr, a := Ua, b := Vb}
        -- assert! defEq
        let UasEqVbs? := UasEqVbs?.push UaEqVb?
        if _h : idx < as.size - 1 then
          loop (idx + 1) aVars bVars Uas Vbs UasEqVbs? ds? us vs
        else
          let ret ← mkAppEqProof? meth aVars bVars us vs Uas Vbs UasEqVbs? ds? as bs asEqbs? f g usedLets' fEqg?
          pure ret

      if let some AEqB := AEqB? then 
        meth.withNewFVar 202 bName B bBi fun bVar => do
          let teqsType := mkAppN (.const `HEq [u]) #[A, aVar.toExpr, B, bVar.toExpr]
          let seqtType := mkAppN (.const `HEq [u]) #[B, bVar.toExpr, A, aVar.toExpr]
          meth.withNewFVar 203 default teqsType.toPExpr default fun vaEqb => do
            meth.withNewFVar 204 default seqtType.toPExpr default fun vbEqa => do
              withEqFVar aVar bVar {aEqb := vaEqb, bEqa := vbEqa, a := (Expr.fvar aVar).toPExpr, b := (Expr.fvar bVar).toPExpr, A := A, B := B, u} do
                let d := (vaEqb, vbEqa, AEqB)
                cont (.some d) bVar
      else
        cont none aVar
  termination_by (as.size - 1) - idx

  if as.size > 0 then
    loop 0 #[] #[] #[] #[] #[] #[] #[] #[]
  else
    pure none

-- TODO generalize so can also be used for lambdas
def binAbs (max : Nat) (tfT' sfT' : Expr) (lambda : Bool) : m
    (Option (PExpr × Array LocalDecl × Array PExpr ×
     PExpr × Array LocalDecl × Array PExpr ×
     Array (Option EExpr) × Std.HashSet Nat)) := do
  let rec loop tfT sfT tDomsVars tDoms sDomsVars sDoms tDomsEqsDoms (absArgs' : Std.HashSet Nat) idx' (origDomVars origDomVarsAbs : Array (FVarId × FVarId)) (origDomVarsRefs : Std.HashMap (FVarId × FVarId) (Std.HashSet (FVarId × FVarId))) (origDomVarsToNewDomVars : Std.HashMap (FVarId × FVarId) (FVarId × FVarId)) := do

    let withMaybeAbs tBod sBod usesPrfIrrel f (tName := `tT) (sName := `sT) (tBi := default) (sBi := default) := do 
      if usesPrfIrrel || origDomVarsAbs.any (tBod.containsFVar' ·.1) || origDomVarsAbs.any (sBod.containsFVar' ·.2) then
        let mut depVars := #[]
        let mut origDepVars := #[]
        let mut origDepVarsSet : Std.HashSet (FVarId × FVarId) := default
        for (tvar, svar) in origDomVars do
          if tBod.containsFVar' tvar || sBod.containsFVar' svar then
            origDepVarsSet := origDepVarsSet.insert (tvar, svar)
            for (tvar', svar') in origDomVarsRefs.get! (tvar, svar) do
              origDepVarsSet := origDepVarsSet.insert (tvar', svar')

        for (tvar, svar) in origDomVars do
          if origDepVarsSet.contains (tvar, svar) then
            depVars := depVars.push $ origDomVarsToNewDomVars.get! (tvar, svar)
            origDepVars := origDepVars.push $ (tvar, svar)

        let tType ← meth.inferTypePure 214 tBod.toPExpr
        let Mt := (← getLCtx).mkForall (depVars.map fun (tvar, _) => (Expr.fvar tvar)) tType
        let MtNamePrefix := tName.getRoot.toString ++ "T" |>.toName
        let MtName := tName.replacePrefix (tName.getRoot) MtNamePrefix
        let sType ← meth.inferTypePure 215 sBod.toPExpr
        let Ms := (← getLCtx).mkForall (depVars.map fun (_, svar) => (Expr.fvar svar)) sType
        let MsNamePrefix := sName.getRoot.toString ++ "T" |>.toName
        let MsName := sName.replacePrefix (sName.getRoot) MsNamePrefix

        meth.withNewFVar 205 MtName Mt.toPExpr tBi fun MtVar => do
          meth.withNewFVar 206 MsName Ms.toPExpr sBi fun MsVar => do
            let tDomsVars := tDomsVars.push MtVar
            let sDomsVars := sDomsVars.push MsVar
            let tDom := (← getLCtx).mkLambda (origDepVars.map fun (tvar, _) => (Expr.fvar tvar)) tBod |>.toPExpr
            let sDom := (← getLCtx).mkLambda (origDepVars.map fun (_, svar) => (Expr.fvar svar)) sBod |>.toPExpr
            let tDoms := tDoms.push tDom
            let sDoms := sDoms.push sDom
            let (true, tDomEqsDom?) ←
              if origDepVars.isEmpty then
                meth.isDefEq 216 tDom sDom
              else
                meth.isDefEqLambda tDom sDom
              | return none
            let tDomsEqsDoms := tDomsEqsDoms.push tDomEqsDom?
            let newtType := Lean.mkAppN (.fvar MtVar) (depVars.map (.fvar ·.1))
            let newsType := Lean.mkAppN (.fvar MsVar) (depVars.map (.fvar ·.2))
            f (.some (newtType, newsType)) tDomsVars sDomsVars tDoms sDoms tDomsEqsDoms
      else
        f none tDomsVars sDomsVars tDoms sDoms tDomsEqsDoms

    let cont tBod sBod := do 
      let (true, tBodEqsBod?) ← meth.isDefEq 0 tBod.toPExpr sBod.toPExpr |
        return none
      withMaybeAbs tBod sBod tBodEqsBod?.isSome fun newtsBod? tDomsVars sDomsVars tDoms sDoms tDomsEqsDoms => do
        let (newtBod, newsBod) := newtsBod?.getD (tBod, sBod)
        let mut newDomVars := #[]
        for tsvar in origDomVars do
          newDomVars := newDomVars.push (origDomVarsToNewDomVars.get! tsvar)
        let tAbsArgs := (newDomVars.map (fun ((tvar, _) : FVarId × FVarId) => .fvar tvar))
        let tAbs ← do
          if lambda then
            pure $ (← getLCtx).mkLambda tAbsArgs newtBod |>.toPExpr
          else
            pure $ (← getLCtx).mkForall tAbsArgs newtBod |>.toPExpr
        let sAbsArgs := (newDomVars.map (fun ((_, svar) : FVarId × FVarId) => .fvar svar))
        let sAbs ← do
          if lambda then
            pure $ (← getLCtx).mkLambda sAbsArgs newsBod |>.toPExpr
          else
            pure $ (← getLCtx).mkForall sAbsArgs newsBod |>.toPExpr
        pure (tAbs, tDomsVars, tDoms, sAbs, sDomsVars, sDoms, tDomsEqsDoms, absArgs')

    if idx' < max then
      match lambda, (← meth.whnfPure 218 tfT.toPExpr).toExpr, (← meth.whnfPure 219 sfT.toPExpr).toExpr with
        | false, .forallE tName tDom tBod tBi, .forallE sName sDom sBod sBi
        | true, .lam tName tDom tBod tBi, .lam sName sDom sBod sBi =>
          let mut refs := default
          for (tvar, svar) in origDomVars do
            if tDom.containsFVar' tvar || sDom.containsFVar' svar then
              refs := refs.insert (tvar, svar)
              for (tvar', svar') in origDomVarsRefs.get! (tvar, svar) do
                refs := refs.insert (tvar', svar')

          let (true, tDomEqsDom?) ← meth.isDefEq 0 tDom.toPExpr sDom.toPExpr | -- FIXME only check usesPrfIrrel here, no need to compute patched term
            return none

          let cont' idt ids := do
            let tBod := tBod.instantiate1 (.fvar idt)
            let sBod := sBod.instantiate1 (.fvar ids)
            let origDomVarsRefs := origDomVarsRefs.insert (idt, ids) refs
            let origDomVars := origDomVars.push (idt, ids)
            withMaybeAbs tDom sDom tDomEqsDom?.isSome (fun newtsDom? tDomsVars sDomsVars tDoms sDoms tDomsEqsDoms => do
                if let some (newtDom, newsDom) := newtsDom? then
                  let origDomVarsAbs := origDomVarsAbs.push (idt, ids)
                  meth.withNewFVar 208 tName newtDom.toPExpr tBi fun idnewt => do
                    meth.withNewFVar 209 sName newsDom.toPExpr sBi fun idnews => do
                      let origDomVarsToNewDomVars := origDomVarsToNewDomVars.insert (idt, ids) (idnewt, idnews)
                      let absArgs' := absArgs'.insert idx'
                      loop tBod sBod tDomsVars tDoms sDomsVars sDoms tDomsEqsDoms absArgs' (idx' + 1) origDomVars origDomVarsAbs origDomVarsRefs origDomVarsToNewDomVars
                else
                  let origDomVarsToNewDomVars := origDomVarsToNewDomVars.insert (idt, ids) (idt, ids)
                  loop tBod sBod tDomsVars tDoms sDomsVars sDoms tDomsEqsDoms absArgs' (idx' + 1) origDomVars origDomVarsAbs origDomVarsRefs origDomVarsToNewDomVars
              )
              tName sName

          meth.withNewFVar 207 tName tDom.toPExpr tBi fun idt => do
            if tDomEqsDom?.isSome then
              meth.withNewFVar 210 sName sDom.toPExpr sBi fun ids => do
                let sort ← meth.inferTypePure 221 tDom.toPExpr
                let .sort lvl := (← meth.ensureSortCorePure sort tDom).toExpr | unreachable!
                let teqsType := mkAppN (.const `HEq [lvl]) #[tDom, (.fvar idt), sDom, (.fvar ids)]
                let seqtType := mkAppN (.const `HEq [lvl]) #[sDom, (.fvar ids), tDom, (.fvar idt)]
                let some tVar := (← getLCtx).find? idt | unreachable!
                let some sVar := (← getLCtx).find? ids | unreachable!
                meth.withNewFVar 211 default teqsType.toPExpr default fun idtEqs => do
                  meth.withNewFVar 212 default seqtType.toPExpr default fun idsEqt => do
                    let some vtEqs := (← getLCtx).find? idtEqs | unreachable!
                    withEqFVar idt ids {aEqb := vtEqs, bEqa := default, a := tVar.toExpr.toPExpr, b := sVar.toExpr.toPExpr, A := tDom.toPExpr, B := sDom.toPExpr, u := lvl} do
                      cont' idt ids
            else
              cont' idt idt
        | _, tBod, sBod =>
          cont tBod sBod
    else
      cont tfT sfT
  loop tfT' sfT' #[] #[] #[] #[] #[] default 0 #[] #[] default default

def forallAbs (max : Nat) (tfT' sfT' : Expr) : m
    (Option (PExpr × Array LocalDecl × Array PExpr ×
     PExpr × Array LocalDecl × Array PExpr ×
     Array (Option EExpr) × Std.HashSet Nat)) := binAbs meth max tfT' sfT' false

def lamAbs (max : Nat) (tfT' sfT' : Expr) : m
    (Option (PExpr × Array LocalDecl × Array PExpr ×
     PExpr × Array LocalDecl × Array PExpr ×
     Array (Option EExpr) × Std.HashSet Nat)) := binAbs meth max tfT' sfT' true

mutual
def deconstructAppHEq' (n : Nat) (t s : PExpr) (tEqs : EExpr) (T? : Option PExpr) : m (Option (Array PExpr × Array PExpr × Array (Option EExpr) × Array (FVarId × Name × PExpr) × Array (FVarId × Name × PExpr) × PExpr × PExpr)) :=
  let defCase := do
    if let some T := T? then
      let tVar := (⟨← meth.mkIdNew 217⟩, default, T)
      let sVar := (⟨← meth.mkIdNew 218⟩, default, T) -- TODO get the names somehow?
      pure $ .some (#[t], #[s], #[.some tEqs], #[tVar], #[sVar], Expr.fvar tVar.1 |>.toPExpr, Expr.fvar sVar.1 |>.toPExpr)
    else pure none
  do match tEqs with
  | .app d => 
    let ret ← deconstructAppHEq d
    if ret.isSome then
      pure ret
    else
      defCase
  | _ => defCase

def deconstructAppHEq : AppData EExpr
  → m (Option (Array PExpr × Array PExpr × Array (Option EExpr) × Array (FVarId × Name × PExpr) × Array (FVarId × Name × PExpr) × PExpr × PExpr))
| {f, a, extra, A, U, ..} => do
  match extra with
  | .UVFun {g, fEqg, ..}            => 
    let some (tas, sas, taEqsas?, tVars, sVars, f', g') ← deconstructAppHEq' 8 f g fEqg none | return none
    return (tas, sas, taEqsas?, tVars, sVars, f'.app a, g'.app a)
  | .Fun {g, fEqg, ..}                 => 
    let some (tas, sas, taEqsas?, tVars, sVars, f', g') ← deconstructAppHEq' 9 f g fEqg (mkForall #[U.2] U.1) | return none
    return (tas, sas, taEqsas?, tVars, sVars, f'.app a, g'.app a)
  | _ => pure ()

  if U.1.containsFVar' U.2 then -- TODO is this too conservative?
    return none

  match extra with
  | .ABUV {g, fEqg, b, aEqb, V, ..} => do
    if V.1.containsFVar' V.2 then
      return none
    let some (tas, sas, taEqsas?, tVars, sVars, f', g') ← deconstructAppHEq' 0 f g fEqg none | return none
    let some (tas', sas', taEqsas?', tVars', sVars', a', b') ← deconstructAppHEq' 1 a b aEqb none | return none
    pure (tas ++ tas', sas ++ sas', taEqsas? ++ taEqsas?', tVars ++ tVars', sVars ++ sVars', f'.app a', g'.app b')
  | .UV {g, fEqg, b, aEqb, V, ..}      =>
    if V.1.containsFVar' V.2 then
      return none
    let some (tas, sas, taEqsas?, tVars, sVars, f', g') ← deconstructAppHEq' 2 f g fEqg none | return none
    let some (tas', sas', taEqsas?', tVars', sVars', a', b') ← deconstructAppHEq' 3 a b aEqb A | return none
    pure (tas ++ tas', sas ++ sas', taEqsas? ++ taEqsas?', tVars ++ tVars', sVars ++ sVars', f'.app a', g'.app b')
  | .AB {g, fEqg, b, aEqb, ..}      => 
    let some (tas, sas, taEqsas?, tVars, sVars, f', g') ← deconstructAppHEq' 4 f g fEqg (mkForall #[U.2] U.1) | return none
    let some (tas', sas', taEqsas?', tVars', sVars', a', b') ← deconstructAppHEq' 5 a b aEqb none | return none
    pure (tas ++ tas', sas ++ sas', taEqsas? ++ taEqsas?', tVars ++ tVars', sVars ++ sVars', f'.app a', g'.app b')
  | .none {g, fEqg, b, aEqb, ..}        => 
    let some (tas, sas, taEqsas?, tVars, sVars, f', g') ← deconstructAppHEq' 6 f g fEqg (mkForall #[U.2] U.1) | return none
    let some (tas', sas', taEqsas?', tVars', sVars', a', b') ← deconstructAppHEq' 7 a b aEqb A | return none
    pure (tas ++ tas', sas ++ sas', taEqsas? ++ taEqsas?', tVars ++ tVars', sVars ++ sVars', f'.app a', g'.app b')
  | .Arg {b, aEqb, ..}                 =>
    let some (tas', sas', taEqsas?', tVars', sVars', a', b') ← deconstructAppHEq' 10 a b aEqb A | return none
    pure (tas', sas', taEqsas?', tVars', sVars', f.app a', f.app b')
  | _ => unreachable!
end

instance : Coe LocalDecl (FVarId × Name × PExpr) where
coe decl := (decl.fvarId, decl.userName, decl.type.toPExpr)

def isDefEqAppOpt''' (tf sf : PExpr) (tArgs sArgs : Array PExpr)
   (targsEqsargs? : Std.HashMap Nat (Option EExpr) := default) (_tfEqsf? : Option (Option EExpr) := none) : m (Bool × (Option (EExpr × Array (Option (PExpr × PExpr × EExpr))))) := do
  unless tArgs.size == sArgs.size do return (false, none)

  let (.true, tfEqsf?) ← if _tfEqsf?.isSome then pure (.true, _tfEqsf?.get!)
    else
      let ret ← meth.isDefEq 222 tf sf
      pure ret
    | return (false, none)

  let mkAppEqProof' tVars sVars tArgs' sArgs' taEqsas' tBodFun sBodFun tBodFunEqsBodFun? tBodArgs sBodArgs _tArgsVars _sArgsVars tBodT sBodT tEtaVars sEtaVars idx := do -- FIXME why do I have to pass in the mutable variables?
    if tVars.size > 0 then
      let tLCtx := tVars.foldl (init := (← getLCtx)) fun acc (id, n, (type : PExpr)) => LocalContext.mkLocalDecl acc id n type default
      let sLCtx := sVars.foldl (init := (← getLCtx)) fun acc (id, n, (type : PExpr)) => LocalContext.mkLocalDecl acc id n type default
      let tVars' := tVars[:tVars.size - tEtaVars].toArray
      let sVars' := sVars[:sVars.size - sEtaVars].toArray
      let tBodArgs' := tBodArgs[:tBodArgs.size - tEtaVars].toArray
      let sBodArgs' := sBodArgs[:sBodArgs.size - sEtaVars].toArray
      let tf' := tLCtx.mkLambda (tVars'.map (.fvar ·.1)) (Lean.mkAppN tBodFun (tBodArgs'.map (·.toExpr)))
      let sf' := sLCtx.mkLambda (sVars'.map (.fvar ·.1)) (Lean.mkAppN sBodFun (sBodArgs'.map (·.toExpr)))
      let mut usedLets' : FVarIdSet := default
      let tfTypeLam := (tLCtx.mkLambda (tVars.map (.fvar ·.1)) tBodT).toPExpr
      -- usedLets' := usedLets'.insert tfTypeLam.toExpr.fvarId!
      let sfTypeLam := (sLCtx.mkLambda (sVars.map (.fvar ·.1)) sBodT).toPExpr
      assert! (← meth.isDefEqLean tfTypeLam sfTypeLam)
      -- usedLets' := usedLets'.insert sfTypeLam.toExpr.fvarId!
      -- let (tfType', sfType') ← meth.alignForAll tArgs.size tfType sfType -- TODO how to put .toPExpr directly on matched vars?
      -- let (defEq, p?) ← meth.isDefEqForall tfType.toPExpr sfType.toPExpr tVars.size fun tfTypeEqsfType? => do
      --   let ret ← mkAppEqProof meth tfType.toPExpr sfType.toPExpr tfTypeEqsfType? tArgs' sArgs' taEqsas' tf'.toPExpr sf'.toPExpr
      --   pure ret -- FIXME reduce redexes in last two values (construct partial application directly)
      -- assert! defEq
      -- withLCtx tLCtx do
      --   let iT ← meth.inferTypePure 1111 (Lean.mkAppN tBodFun (tBodArgs'.map (·.toExpr))).toPExpr -- sanity check
      --   let T := tLCtx.mkForall (tVars[sBodArgs.size - sEtaVars:].toArray.map (.fvar ·.1)) tBodT
      --   if not (← meth.isDefEqPure 209 T.toPExpr iT) then
      if tBodFunEqsBodFun?.isSome then -- FIXME need to handle this case?
        assert! (← meth.isDefEqPure 55500 tf'.toPExpr sf'.toPExpr)

      let getVarLams vars lctx := do
        let mut ret := #[]
        let mut varsToIdxs : Array (Std.HashSet Nat) := #[]
        let mut i := 0
        for (_, _, type) in vars do
          let mut varToIdxs : Std.HashSet Nat := default
          let mut di := 0
          for prevVar in vars[:i] do
            let pid := prevVar.1
            if type.toExpr.containsFVar' pid then
              varToIdxs := varToIdxs.insert di
              varToIdxs := varToIdxs.union (varsToIdxs[di]!)
            di := di + 1
          varsToIdxs := varsToIdxs.push varToIdxs
          i := i + 1

        i := 0
        for (_, n, type) in vars do
          let varToIdx := varsToIdxs[i]!
          let mut depVars := #[]
          let mut depVarIdxs := #[]
          let mut di := 0
          for prevVar in vars[:i] do
            if varToIdx.contains di then
              depVars := depVars.push prevVar
              depVarIdxs := depVarIdxs.push di
            di := di + 1
          let lam := (lctx.mkLambda (depVars.map (.fvar ·.1)) type).toPExpr
          ret := ret.push (depVarIdxs, n, default, lam)
          i := i + 1
        pure ret

      let tVarLams ← getVarLams tVars tLCtx
      let sVarLams ← getVarLams sVars sLCtx
      -- for (_, _, _, lam) in tVarLams ++ sVarLams do
      --   usedLets' := usedLets'.insert lam.toExpr.fvarId!

      let p? ← mkAppEqProof meth tfTypeLam sfTypeLam tVarLams sVarLams none tArgs' sArgs' taEqsas' tf'.toPExpr sf'.toPExpr usedLets'
      pure p?
    else
      pure none

  let getELCtx (vars : Array (FVarId × Name × PExpr)) := do
    pure $ vars.foldl (init := (← getLCtx)) fun acc ((v, n, T) ) => acc.mkLocalDecl v n T

  let mut taEqsaDatas := #[]

  let mut tBodFun : PExpr := tf
  let mut tBodArgs : Array PExpr := #[]
  let mut sBodFun : PExpr := sf
  let mut tBodFunEqsBodFun? := tfEqsf?
  let mut sBodArgs : Array PExpr := #[]
  let mut tArgs' := #[]
  let mut tArgsIs' : Array Nat := #[]
  let mut sArgs' := #[]
  let mut sArgsIs' : Array Nat := #[]
  let mut tVars : Array (FVarId × Name × PExpr) := #[]
  let mut sVars : Array (FVarId × Name × PExpr) := #[]
  let mut tArgsVars : Array FVarId := #[]
  let mut sArgsVars : Array FVarId := #[]
  let mut tEtaVars : Nat := 0 -- number of vars that can be eliminated from the lambda by eta reduction
  let mut sEtaVars : Nat := 0
  let mut absArgs : Std.HashSet Nat := default
  let mut tfT ← meth.inferTypePure 223 tBodFun -- FIXME avoid when possible
  let mut sfT ← meth.inferTypePure 224 sBodFun
  let mut tBodT := tfT
  let mut sBodT := sfT
  let mut taEqsas' := #[]

  for idx in [:tArgs.size] do
    let (tBodDom, tDomName, sBodDom, sDomName) ← do
      let ok? ←
        if idx == 0 && tfEqsf?.isSome then
          pure none
        else
          let tBodT' ← meth.whnfPure 225 tBodT
          let sBodT' ← meth.whnfPure 226 sBodT
          match tBodT'.toExpr, sBodT'.toExpr with
            | .forallE tDomName tDom _ _, .forallE sDomName sDom _ _ =>
              let tDom' := (← meth.whnfPure 239 tDom.toPExpr) |>.toExpr
              let sDom' := (← meth.whnfPure 240 sDom.toPExpr) |>.toExpr
              -- let tDom' := tDom
              -- let sDom' := sDom
              if tArgsVars.any fun id => tDom'.containsFVar' id || sArgsVars.any fun id => sDom'.containsFVar' id then
                absArgs := absArgs.insert idx
              pure $ .some (tDom, tDomName, sDom, sDomName)
            | _, _ => pure none

      if let .some (tBodDom, tDomName, sBodDom, sDomName) := ok? then
        pure (tBodDom.toPExpr, tDomName, sBodDom.toPExpr, sDomName)
      else -- the current partial application needs to be abstracted as a function
        let tfEqsf'? ←
          if idx == 0 && tfEqsf?.isSome then
            pure (tfEqsf?)
          else
            mkAppEqProof' tVars sVars tArgs' sArgs' taEqsas' tBodFun sBodFun tBodFunEqsBodFun? tBodArgs sBodArgs tArgsVars sArgsVars tBodT sBodT tEtaVars sEtaVars idx
        let tf := (Lean.mkAppN tf (tArgs[:idx].toArray.map (·.toExpr))).toPExpr
        let sf := (Lean.mkAppN sf (sArgs[:idx].toArray.map (·.toExpr))).toPExpr

        -- TODO
        let (tfVar, tfTAbsDomsVars, tfTAbsDoms, sfVar, sfTAbsDomsVars, sfTAbsDoms, tfTAbsDomsEqsfTAbsDoms?, absArgs') ← do
          -- if (← meth.shouldTTrace) then
          --   dbg_trace s!"DBG[A]: App.lean:495 (after if (← meth.shouldTTrace) then)"
          --   _ ← meth.isDefEqLean tfT sfT
          --   dbg_trace s!"DBG[B]: App.lean:497 (after sorry)"
          --   _ ← meth.isDefEq 0 tfT sfT
          --   dbg_trace s!"DBG[C]: App.lean:498"
          -- meth.ttrace s!"DBG[4]: App.lean:500 (after dbg_trace s!DBG[C]: App.lean:498)"
          let (.some (tfType, tfTAbsDomsVars, tfTAbsDoms, sfType, sfTAbsDomsVars, sfTAbsDoms, tfTAbsDomsEqsfTAbsDoms?, absArgsOffset')) ← forallAbs meth (tArgs.size - idx) tfT.toExpr sfT.toExpr | return (false, none)
          -- meth.ttrace s!"DBG[5]: App.lean:502 (after let (.some (tfType, tfTAbsDomsVars, tfTA…)"
          let mut absArgs' := default
          for pos in absArgsOffset' do
            absArgs' := absArgs'.insert (pos + idx)
          let tfVar := (⟨← meth.mkId' 213 (← getELCtx (tfTAbsDomsVars.map (Coe.coe ·))) tfType⟩, `f, tfType)
          let sfVar := (⟨← meth.mkId' 214 (← getELCtx (sfTAbsDomsVars.map (Coe.coe ·))) sfType⟩, `g, sfType)
          pure (tfVar, tfTAbsDomsVars, tfTAbsDoms, sfVar, sfTAbsDomsVars, sfTAbsDoms, tfTAbsDomsEqsfTAbsDoms?, absArgs')

        tBodFun := Expr.fvar tfVar.1 |>.toPExpr
        sBodFun := Expr.fvar sfVar.1 |>.toPExpr
        tBodArgs := #[]
        sBodArgs := #[]
        tBodT := tfVar.2.2
        sBodT := sfVar.2.2
        taEqsas' := tfTAbsDomsEqsfTAbsDoms? ++ #[tfEqsf'?]
        tArgs' := tfTAbsDoms ++ #[tf]
        tArgsIs' := List.replicate tfTAbsDoms.size 0 |>.toArray
        tArgsIs' := tArgsIs' ++ #[1]
        sArgs' := sfTAbsDoms ++ #[sf]
        sArgsIs' := List.replicate sfTAbsDoms.size 0 |>.toArray
        sArgsIs' := sArgsIs' ++ #[1]
        tArgsVars := #[]
        sArgsVars := #[]
        tVars := (tfTAbsDomsVars.map fun v => (v.fvarId, v.userName, v.type.toPExpr)) ++ #[tfVar]
        sVars := (sfTAbsDomsVars.map fun v => (v.fvarId, v.userName, v.type.toPExpr)) ++ #[sfVar]
        tEtaVars := 0
        sEtaVars := 0
        absArgs := absArgs'

        let tBodT' ← meth.whnfPure 227 tBodT
        let sBodT' ← meth.whnfPure 228 sBodT
        match tBodT'.toExpr, sBodT'.toExpr with
          | .forallE tDomName tDom _ _, .forallE sDomName sDom _ _ =>
            pure $ (tDom.toPExpr, tDomName, sDom.toPExpr, sDomName)
          | _, _ => unreachable!
    let ta := tArgs[idx]!
    let sa := sArgs[idx]!

    let mut taEqsa? := none
    if let some _p? := targsEqsargs?.get? idx then
      taEqsa? := _p?
    else
      -- if (← meth.shouldTTrace) && (idx == 3) then
      --   dbg_trace s!"DBG[0]: App.lean:521 {← meth.numCalls}"
      let (.true, _p?) ← meth.isDefEq 229 ta sa | return (false, none)
      -- meth.ttrace s!"DBG[2]: App.lean:521 {idx}, {_p?.isSome}, {ta}, {sa}"
      -- if (← meth.shouldTTrace) && (idx == 3) then
      --   meth.ttrace s!"DBG[3]: App.lean:521 {← meth.isDefEqPure 0 ta sa}"
      taEqsa? := _p?
    let taEqsaData? := taEqsa?.map (ta, sa, ·)
    taEqsaDatas := taEqsaDatas.push taEqsaData?

    let (tBoda, sBoda) ← if taEqsa?.isSome || absArgs.contains idx then
      let getDefVals := do
        let tVar := (⟨← meth.mkId' 215 (← getELCtx tVars) tBodDom⟩, tDomName, tBodDom)
        let sVar := (⟨← meth.mkId' 216 (← getELCtx sVars) sBodDom⟩, sDomName, sBodDom)
        pure ((#[ta], #[sa], #[taEqsa?], #[tVar], #[sVar], Expr.fvar tVar.1 |>.toPExpr, Expr.fvar sVar.1 |>.toPExpr), tEtaVars + 1, sEtaVars + 1)
      let ((tas', sas', taEqsas'?, tVars', sVars', tBoda', sBoda'), tEtaVars', sEtaVars') ←
        if not (absArgs.contains idx) then -- TODO should we do an abstraction of the partial application here instead?
          if let some taEqsa := taEqsa? then
            match taEqsa with
            | .app d =>
              let some (tas', sas', taEqsas'?, tVars', sVars', tBoda', sBoda') ← deconstructAppHEq meth d | getDefVals
              let mut tVars'' := tVars
              let mut newtVars' := #[]
              for i in [:tVars'.size] do
                let (_, n, T) := tVars'[i]!
                let newId := ⟨← meth.mkId' 219 (← getELCtx tVars'') T⟩
                newtVars' := newtVars'.push (newId, n, T)
                tVars'' := tVars''.push (newId, n, T)
              let mut sVars'' := sVars
              let mut newsVars' := #[]
              for i in [:sVars'.size] do
                let (_, n, T) := sVars'[i]!
                let newId := ⟨← meth.mkId' 219 (← getELCtx sVars'') T⟩
                newsVars' := newsVars'.push (newId, n, T)
                sVars'' := sVars''.push (newId, n, T)
              let newtBoda' := tBoda'.toExpr.replaceFVars (tVars'.map fun (id, _, _) => .fvar id) (newtVars'.map fun (id, _, _) => .fvar id) |>.toPExpr
              let newsBoda' := sBoda'.toExpr.replaceFVars (sVars'.map fun (id, _, _) => .fvar id) (newsVars'.map fun (id, _, _) => .fvar id) |>.toPExpr

              -- let (tas', sas', taEqsas'?, tVars', sVars', tBoda', sBoda') := ret
              -- let tLCtx := (tVars ++ tVars').foldl (init := (← getLCtx)) fun acc (id, n, (type : PExpr)) => LocalContext.mkLocalDecl acc id n type default

              -- withLCtx tLCtx do
              --   try
              --     _ ← meth.inferTypePure 2222 tBoda' -- sanity check
              --   catch ex =>
              --     throw ex
              pure ((tas', sas', taEqsas'?, newtVars', newsVars', newtBoda', newsBoda'), 0, 0) -- TODO why does this make the extra parentheses necessary in the match above?
            | _ => getDefVals
          else
            getDefVals
        else
          getDefVals
          -- dbg_trace s!"DBG[A]: TypeChecker.lean:440 {← meth.isDefEqPure 0 aEqbType (← meth.inferTypePure 0 aEqb)}"
          -- _ ← meth.inferTypeCheck (EExpr.app {u, v, A, U, f, a, extra := ret}).toExpr.toPExpr
          -- dbg_trace s!"DBG[B]: TypeChecker.lean:481 (after _ ← inferTypeCheck p)"
          -- sorry

      tArgs' := tArgs' ++ tas'
      tArgsIs' := tArgsIs' ++ List.replicate tas'.size 2
      sArgs' := sArgs' ++ sas'
      sArgsIs' := sArgsIs' ++ List.replicate sas'.size 2
      taEqsas' := taEqsas' ++ taEqsas'?

      tVars := tVars ++ tVars'
      sVars := sVars ++ sVars'
      tArgsVars := tArgsVars ++ (tVars'.map (·.1))
      sArgsVars := sArgsVars ++ (sVars'.map (·.1))
      tEtaVars := tEtaVars'
      sEtaVars := sEtaVars'

      pure (tBoda', sBoda')
    else 
      tEtaVars := 0
      sEtaVars := 0
      pure (ta, sa)

    tBodArgs := tBodArgs.push tBoda
    sBodArgs := sBodArgs.push sBoda

    (tfT, sfT) ← match (← meth.whnfPure 230 tfT).toExpr, (← meth.whnfPure 231 sfT).toExpr with
      | .forallE _ _ tBody _, .forallE _ _ sBody _ =>
        if taEqsa?.isNone then
          pure $ (tBody.instantiate1 ta |>.toPExpr, sBody.instantiate1 ta |>.toPExpr)
        else
          pure $ (tBody.instantiate1 ta |>.toPExpr, sBody.instantiate1 sa |>.toPExpr)
      | _, _ => unreachable!

    (tBodT, sBodT) ← match (← meth.whnfPure 232 tBodT).toExpr, (← meth.whnfPure 233 sBodT).toExpr with
      | .forallE _ _ tBody _, .forallE _ _ sBody _ =>
        pure $ (tBody.instantiate1 tBoda |>.toPExpr, sBody.instantiate1 sBoda |>.toPExpr)
      | _, _ => unreachable!

  let tEqs? ← mkAppEqProof' tVars sVars tArgs' sArgs' taEqsas' tBodFun sBodFun tBodFunEqsBodFun? tBodArgs sBodArgs tArgsVars sArgsVars tBodT sBodT tEtaVars sEtaVars tArgs'.size
  -- TODO(perf) restrict data collection to the case of `taEqsa?.isSome || ret?.isSome`
  return (true, (tEqs?.map fun tEqs => (tEqs, taEqsaDatas)))

-- def isDefEqApp''' (tf sf : PExpr) (tArgs sArgs : Array PExpr)
--    (targsEqsargs? : Std.HashMap Nat (Option EExpr) := default) (tfEqsf? : Option (Option EExpr) := none) : m (Bool × (Option (EExpr × Array (Option (PExpr × PExpr × EExpr))))) := do
--   unless tArgs.size == sArgs.size do return (false, none)
--
--   let (.true, _ret?) ← if tfEqsf?.isSome then pure (.true, tfEqsf?.get!)
--     else meth.isDefEq 234 tf sf | return (false, none)
--
--   let mut taEqsas := #[]
--   let mut idx := 0
--   for ta in tArgs, sa in sArgs do
--     let mut p? := none
--     if let some _p? := targsEqsargs?[idx]? then
--       p? := _p?
--     else
--       let (.true, _p?) ← meth.isDefEq 235 ta sa | return (false, none)
--       p? := _p?
--     taEqsas := taEqsas.push (p?.map (ta, sa, ·))
--     idx := idx + 1
--
--   let mut tfT ← meth.inferTypePure 236 tf
--   let mut sfT ← meth.inferTypePure 237 sf
--   -- let (tfT', sfT') ← meth.alignForAll tArgs.size tfT sfT -- TODO how to put .toPExpr directly on matched vars?
--   -- let (defEq, tEqs?) ← meth.isDefEqForall tfT'.toPExpr sfT'.toPExpr tArgs.size fun tfTEqsfT? =>
--   --   mkAppEqProof meth tfT sfT tfTEqsfT? tArgs sArgs (taEqsas.map (·.map (·.2.2))) tf sf _ret?
--   -- assert! defEq
--   let tEqs? ← mkAppEqProof meth tfT sfT none tArgs sArgs (taEqsas.map (·.map (·.2.2))) tf sf _ret?
--
--   -- TODO(perf) restrict data collection to the case of `taEqsa?.isSome || ret?.isSome`
--   return (true, (tEqs?.map fun tEqs => (tEqs, taEqsas)))

def isDefEqApp'' (tf sf : PExpr) (tArgs sArgs : Array PExpr)
   (targsEqsargs? : Std.HashMap Nat (Option EExpr) := default) (tfEqsf? : Option (Option EExpr) := none) : m (Bool × (Option (EExpr × Array (Option (PExpr × PExpr × EExpr))))) := do
  -- if meth.opt then
  isDefEqAppOpt''' meth tf sf tArgs sArgs targsEqsargs? tfEqsf?
  -- else
    -- isDefEqApp''' meth tf sf tArgs sArgs targsEqsargs? tfEqsf?
end App
