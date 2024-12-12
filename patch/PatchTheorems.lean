prelude
import Init.Prelude
import Init.Notation
import Init.Core
-- import Lean4Less.Commands

namespace L4L

universe u v

axiom prfIrrel {P : Prop} (p q : P) : Eq p q

/- --- --- bootstrapping lemmas --- --- -/

theorem appArgEq {A : Sort u} {U : Sort v}
  (f : (a : A) → U)
  {a b : A} (hab : Eq a b)
  : Eq (f a) (f b) := by
  subst hab
  rfl

theorem forallEqUV' {A : Sort u} {U V : A → Sort v}
  (hUV : (a : A) → Eq (U a) (V a))
  : Eq ((a : A) → U a) ((b : A) → V b) := by
  have : Eq U V := by
    apply funext
    intro x
    exact hUV x
  subst this
  rfl

-- axiom eq_of_heq {A : Sort u} {a b : A} (h : HEq a b) : @Eq A a b

theorem eq_of_heq {A : Sort u} {a b : A} (h : HEq a b) : @Eq A a b := -- NOTE: this lemma has been manually translated to Lean-
  -- TODO clean this up
  let_fun this := fun (A B : Sort u) (a : A) (b : B) (hab : HEq a b) =>
    @HEq.rec A a
      (@fun (B : Sort u) (b : B) _ =>
        ∀ (hAB : @Eq (Sort u) A B), @Eq B (@cast A B hAB a) b)
      (@cast (∀ (hAA : @Eq (Sort u) A A), @Eq A (@cast A A hAA a) (@cast A A hAA a))
        ((fun (B : Sort u) (b : B) _ =>
            ∀ (hAB : @Eq (Sort u) A B), @Eq B (@cast A B hAB a) b)
          A a (@HEq.refl A a))
        (@L4L.forallEqUV' (@Eq (Sort u) A A)
          (fun (hAA : @Eq (Sort u) A A) => @Eq A (@cast A A hAA a) (@cast A A hAA a))
          (fun (hAA : @Eq (Sort u) A A) => @Eq A (@cast A A hAA a) a) fun (hAA : @Eq (Sort u) A A) =>
          let p :=
            @L4L.appArgEq (@Eq (Sort u) A A)
              A
              (@Eq.rec (Sort u) A (fun (B : Sort u) _ => B) a A) hAA (@Eq.refl (Sort u) A)
              (@L4L.prfIrrel (@Eq (Sort u) A A) hAA (@Eq.refl (Sort u) A));
          @L4L.appArgEq A Prop (@Eq A (@cast A A hAA a)) (@cast A A hAA a) a p)
        fun (hAA : @Eq (Sort u) A A) => @rfl A (@cast A A hAA a))
      B b hab;
  this A A a b h (@rfl (Sort u) A)

-- #check_off L4L.eq_of_heq

/- --- --- congruence lemmas --- --- -/

--- forall ---

theorem forallHEqABUV' {A B : Sort u} {U : A → Sort v} {V : B → Sort v}
  (hAB : HEq A B) (hUV : (a : A) → (b : B) → HEq a b → HEq (U a) (V b))
  : HEq ((a : A) → U a) ((b : B) → V b) := by
  have h := eq_of_heq hAB -- TODO define a macro for this
  subst h
  have : Eq U V := by
    apply funext
    intro x
    exact eq_of_heq $ hUV x x HEq.rfl
  subst this
  rfl

theorem forallHEqABUV {A B : Sort u} {U V : Sort v}
  (hAB : HEq A B) (hUV : HEq U V)
  : HEq ((a : A) → U) ((b : B) → V) := by
  apply forallHEqABUV' hAB fun _ _ _ => hUV

theorem forallHEqUV {A : Sort u} {U V : Sort v}
  (hUV : HEq U V)
  : HEq ((a : A) → U) ((b : A) → V) := by
  apply forallHEqABUV HEq.rfl hUV

theorem forallHEqUV' {A : Sort u} {U V : A → Sort v}
  (hUV : (a : A) → HEq (U a) (V a))
  : HEq ((a : A) → U a) ((b : A) → V b) := by
  refine forallHEqABUV' HEq.rfl fun a b hab => ?_
  have h := eq_of_heq hab
  subst h
  exact hUV a

theorem forallHEqAB {A B : Sort u} {U : Sort v} (hAB : HEq A B)
  : HEq ((a : A) → U) ((b : B) → U) := by
  apply forallHEqABUV hAB HEq.rfl

--- lambda ---

theorem lambdaHEqABUV' {A B : Sort u} {U : A → Sort v} {V : B → Sort v}
  (f : (a : A) → U a) (g : (b : B) → V b)
  (hAB : HEq A B) (hfg : (a : A) → (b : B) → HEq a b → HEq (f a) (g b))
  : HEq (fun a => f a) (fun b => g b) := by
  have h := eq_of_heq hAB
  subst h
  have : Eq U V := by
    apply funext
    intro x
    exact type_eq_of_heq (hfg x x (@HEq.rfl A x))
  subst this
  apply heq_of_eq
  apply funext
  intro x
  apply eq_of_heq
  apply hfg
  rfl

theorem lambdaHEqABUV {A B : Sort u} {U V : Sort v}
  (f : (a : A) → U) (g : (b : B) → V)
  (hAB : HEq A B) (hfg : (a : A) → (b : B) → HEq a b → HEq (f a) (g b))
  : HEq (fun a => f a) (fun b => g b) := by
  apply lambdaHEqABUV' _ _ hAB hfg

theorem lambdaHEqUV' {A : Sort u} {U V : A → Sort v}
  {f : (a : A) → U a} {g : (b : A) → V b}
  (hfg : (a : A) → HEq (f a) (g a))
  : HEq (fun a => f a) (fun b => g b) := by
  apply lambdaHEqABUV' _ _ HEq.rfl
  intro a b hab
  have h := eq_of_heq hab
  subst h
  exact hfg a

theorem lambdaHEqUV {A : Sort u} {U V : Sort v}
  {f : (a : A) → U} {g : (b : A) → V}
  (hfg : (a : A) → HEq (f a) (g a))
  : HEq (fun a => f a) (fun b => g b) := by
  apply lambdaHEqUV' hfg

theorem lambdaHEq' {A : Sort u} {U : A → Sort v}
  {f g : (a : A) → U a}
  (hfg : (a : A) → HEq (f a) (g a))
  : HEq (fun a => f a) (fun b => g b) := by
  apply lambdaHEqUV' hfg

theorem lambdaHEq {A : Sort u} {U : Sort v}
  {f g : (a : A) → U}
  (hfg : (a : A) → HEq (f a) (g a))
  : HEq (fun a => f a) (fun b => g b) := by
  apply lambdaHEq' hfg

--- application --- 

theorem appHEqABUV' {A B : Sort u} {U : A → Sort v} {V : B → Sort v}
  (hAB : HEq A B) (hUV : (a : A) → (b : B) → HEq a b → HEq (U a) (V b))
  {f : (a : A) → U a} {g : (b : B) → V b} {a : A} {b : B}
  (hfg : HEq f g) (hab : HEq a b)
  : HEq (f a) (g b) := by
  have h := eq_of_heq hAB
  subst h
  have : Eq U V := by
    apply funext
    intro x
    exact eq_of_heq $ hUV x x HEq.rfl
  subst this
  have h := (eq_of_heq hfg)
  subst h
  have h := (eq_of_heq hab)
  subst h
  rfl

theorem appHEqABUV {A B : Sort u} {U V : Sort v}
  (hAB : HEq A B) (hUV : HEq U V)
  {f : (a : A) → U} {g : (b : B) → V} {a : A} {b : B}
  (hfg : HEq f g) (hab : HEq a b)
  : HEq (f a) (g b) := by
  apply appHEqABUV' hAB (fun _ _ _ => hUV) hfg hab

theorem appHEqUV' {A : Sort u} {U V : A → Sort v}
  (hUV : (a : A) → HEq (U a) (V a))
  {f : (a : A) → U a} {g : (b : A) → V b} {a : A} {b : A}
  (hfg : HEq f g) (hab : HEq a b)
  : HEq (f a) (g b) := by
  refine appHEqABUV' HEq.rfl (fun a b hab => ?_) hfg hab
  have h := eq_of_heq hab
  subst h
  exact hUV a

theorem appHEqUV {A : Sort u} {U V : Sort v}
  (hUV : HEq U V)
  {f : (a : A) → U} {g : (b : A) → V} {a : A} {b : A}
  (hfg : HEq f g) (hab : HEq a b)
  : HEq (f a) (g b) := by
  apply appHEqUV' (fun _ => hUV) hfg hab

theorem appHEqAB {A B : Sort u} {U : Sort v}
  (hAB : HEq A B)
  {f : (a : A) → U} {g : (b : B) → U} {a : A} {b : B}
  (hfg : HEq f g) (hab : HEq a b)
  : HEq (f a) (g b) := by
  apply appHEqABUV hAB HEq.rfl hfg hab

theorem appFunHEqUV' {A : Sort u} {U V : A → Sort v}
  (hUV : (a : A) → HEq (U a) (V a))
  {f : (a : A) → U a} {g : (b : A) → V b} (a : A)
  (hfg : HEq f g)
  : HEq (f a) (g a) := by
  apply appHEqUV' hUV hfg HEq.rfl

theorem appFunHEqUV {A : Sort u} {U V : Sort v}
  (hUV : HEq U V)
  {f : (a : A) → U} {g : (b : A) → V} (a : A)
  (hfg : HEq f g)
  : HEq (f a) (g a) := by
  apply appHEqUV hUV hfg HEq.rfl

theorem appHEq' {A : Sort u} {U : A → Sort v}
  {f g : (a : A) → U a} {a b : A}
  (hfg : HEq f g) (hab : HEq a b)
  : HEq (f a) (g b) := by
  apply appHEqUV' (fun _ => HEq.rfl) hfg hab

theorem appHEq {A : Sort u} {U : Sort v}
  {f g : (a : A) → U} {a b : A}
  (hfg : HEq f g) (hab : HEq a b)
  : HEq (f a) (g b) := by
  apply appHEq' hfg hab

theorem appFunHEq' {A : Sort u} {U : A → Sort v}
  {f g : (a : A) → U a} (a : A)
  (hfg : HEq f g)
  : HEq (f a) (g a) := by
  apply appHEq' hfg HEq.rfl

theorem appFunHEq {A : Sort u} {U : Sort v}
  {f g : (a : A) → U} (a : A)
  (hfg : HEq f g)
  : HEq (f a) (g a) := by
  apply appFunHEq' a hfg

theorem appArgHEq' {A : Sort u} {U : A → Sort v}
  (f : (a : A) → U a)
  {a b : A} (hab : HEq a b)
  : HEq (f a) (f b) := by
  apply appHEq' HEq.rfl hab

theorem appArgHEq {A : Sort u} {U : Sort v}
  (f : (a : A) → U)
  {a b : A} (hab : HEq a b)
  : HEq (f a) (f b) := by
  apply appArgHEq' f hab

theorem appHEqBinNatFn {N : Type} {T : Type}
  {f : N → N → T} {a1 a2 : N} {b1 b2 : N}
  (ha : HEq a1 a2)
  (hb : HEq b1 b2)
  : HEq (f a1 b1) (f a2 b2) := by
  apply appHEq
  apply appArgHEq
  assumption
  assumption

/- --- --- patching constants --- --- -/

-- axiom forallEqABUV' {A B : Sort u} {U : A → Sort v} {V : B → Sort v}
--   (hAB : Eq A B) (hUV : (a : A) → (b : B) → HEq a b → Eq (U a) (V b))
--   : Eq ((a : A) → U a) ((b : B) → V b)

-- axiom forallEqAB {A B : Sort u} {U : Sort v}
--   (hAB : Eq A B)
--   : Eq ((a : A) → U) ((b : B) → U)

-- axiom appFunEq {A : Sort u} {U : Sort v}
--   {f g : (a : A) → U} (a : A)
--   (hfg : Eq f g)
--   : Eq (f a) (g a)

-- axiom appFunEq' {A : Sort u} {U : A → Sort v}
--   {f g : (a : A) → U a} (a : A)
--   (hfg : Eq f g)
--   : Eq (f a) (g a)

-- axiom appEq {A : Sort u} {U : Sort v}
--   {f g : A → U} {a b : A}
--   (hfg : Eq f g) (hab : Eq a b)
--   : Eq (f a) (g b)

-- axiom appEqAB {A B : Sort u} {U : Sort v}
--   (hAB : Eq A B)
--   {f : (a : A) → U} {g : (b : B) → U} {a : A} {b : B}
--   (hfg : HEq f g) (hab : HEq a b)
--   : Eq (f a) (g b)

-- axiom lambdaEq {A : Sort u} {U : Sort v}
--   (f g : (a : A) → U)
--   (hfg : (a : A) → Eq (f a) (g a))
--   : Eq (fun a => f a) (fun b => g b)

-- axiom lambdaEq' {A : Sort u} {U : A → Sort v}
--   (f g : (a : A) → U a)
--   (hfg : (a : A) → Eq (f a) (g a))
--   : Eq (fun a => f a) (fun b => g b)

theorem prfIrrelHEq {P : Prop} (p q : P) : HEq p q := by
  apply heq_of_eq
  exact prfIrrel _ _

theorem prfIrrelHEqPQ {P Q : Prop} (hPQ : HEq P Q) (p : P) (q : Q) : HEq p q := by
  have h := eq_of_heq hPQ
  subst h
  exact prfIrrelHEq _ _

def castHEq {α β : Sort u} (h : HEq α β) (a : α) : β := cast (eq_of_heq h) a

-- axiom castOrigHEq {α β : Sort u} (h : HEq α β) (a : α) : HEq (castHEq h a) a

def castOrigHEq {α β : Sort u} (h : HEq α β) (a : α) : HEq (castHEq h a) a := by
  have h := eq_of_heq h
  subst h
  rfl

def HEqRefl (_n : Nat) {α : Sort u} (a : α) : HEq a a := HEq.refl a

end L4L
