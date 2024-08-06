prelude
import Init.Prelude
import Init.Notation
import Init.Core

namespace L4L

universe u v

axiom forallHEq {A B : Sort u} {U : A → Sort v} {V : B → Sort v}
  (hAB : A = B) (hUV : (a : A) → (b : B) → HEq a b → HEq (U a) (V b))
  : ((a : A) → U a) = ((b : B) → V b)

axiom prfIrrelHEq (P Q : Prop) (heq : P = Q) (p : Q) (q : P) : HEq p q

axiom appArgHEq {A : Sort u} {U : A → Sort v}
  (f : (a : A) → U a)
  {a b : A} (hab : HEq a b)
  : HEq (f a) (f b)

-- axiom forallHEq {A B : Sort u} {U : A → Sort v} {V : B → Sort v} (hAB : A = B) (hUV : (a : A) → (b : B) → HEq a b → HEq (U a) (V b))
--   : ((a : A) → U a) = ((b : B) → V b)

axiom appHEq' {A : Sort u} {U : A → Sort v}
  {f g : (a : A) → U a} {a b : A}
  (hfg : HEq f g) (hab : HEq a b)
  : HEq (f a) (g b)

axiom appHEq {A B : Sort u} {U : A → Sort v} {V : B → Sort v}
  (hAB : A = B) (hUV : (a : A) → (b : B) → HEq a b → HEq (U a) (V b))
  {f : (a : A) → U a} {g : (b : B) → V b} {a : A} {b : B}
  (hfg : HEq f g) (hab : HEq a b)
  : HEq (f a) (g b)

axiom appHEqBinNatFn {N : Type} {T : Type}
  {f : N → N → T} {a1 a2 : N} {b1 b2 : N}
  (ha : HEq a1 a2)
  (hb : HEq b1 b2)
  : HEq (f a1 b1) (f a2 b2)

axiom lambdaHEq {A B : Sort u} {U : A → Sort v} {V : B → Sort v}
  (f : (a : A) → U a) (g : (b : B) → V b)
  (hAB : A = B) (hfg : (a : A) → (b : B) → HEq a b → HEq (f a) (g b))
  : HEq (fun a => f a) (fun b => g b)

end L4L
