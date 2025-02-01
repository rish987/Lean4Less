import patch.PatchTheorems
import Lean4Less.Commands

inductive K : Prop where
| mk : K

inductive I : Nat → Type where
| l (b : Bool) (n : Nat) : I n
| r (n : Nat) : I n

inductive E : Type where
| a : Nat → E
| b : E

inductive T : Nat → Nat → Prop where
| mk : (n : Nat) → T n n

-- #print T.rec
/-
T.rec.{u} : {n : Nat} →
  {C : (n' : Nat) → T n n' → Sort u} →
    C n (T.mk n) → {n' : Nat} → (t : T n n') →
      C n' t
-/

-- (pretend that `x` and `y` are large, inlined expression that take a long time to typecheck)
axiom x___ : Nat
axiom y___ : Nat

abbrev C := fun m => (n : Nat) → T n (n + m)

noncomputable def r (m : Nat) (c : C m) (i : I m) : Bool :=
  @T.rec x___ (fun _ _ => Bool) (i.rec (fun b _ => b) (fun _ => false)) (x___ + m) (c x___)

@[reducible]
noncomputable def g (fn : Nat → E) (m : Nat) (c : C m) (i : I m) (n : Nat) : Bool :=
(fn n).rec
  (fun _ => false) -- .a _ => ..
  (@T.rec y___ (fun _ _ => Bool) (r m c i) (y___ + m) (c y___)) -- .b => ..
set_option pp.all true in

def F : E → Type
| .a m => (c : C m) → (i : I m) → E → Bool
| .b => Bool

noncomputable def f (fn : Nat → E) : (e : E) → F e
| .a m =>
  fun (c : C m) (i : I m) (e : E) => match e with
  | .a n => m.rec (motive := fun _ => Bool) (g fn m c i n) (fun _ _ => false)
  | .b => false
| .b => .true

def fn : Nat → E
| .zero => .b
| _ => .a 0

noncomputable def ex (k : K) : K.rec 0 k = 0 := rfl
-- partial WHNF
noncomputable def fpr (k : K) (c : C 0) : f (fun (n : Nat) => n.rec (.b) (fun _ _ => .a 0)) (.a 0) c (.l true 0) (.a (K.rec 0 k)) = r 0 c (.l true 0) := rfl
#check_l4l fpr

-- full WHNF
noncomputable def fp (k : K) (c : C 0) : f fn (.a 0) c (.l true 0) (.a (K.rec 0 k)) = true := rfl
#check_l4l fp
-- translation should use the same auxiliary function as `fp`
noncomputable def fp' (c : C 0) : f fn (.a 0) c (.l true 0) (.a 0) = true := rfl


def T.rec_aux {n : Nat}
  {M : (m : Nat) → T n m → Sort u}
    (mtv : M n (T.mk n)) {m : Nat} (t : T n m) (p : n = m) :
      HEq (@T.rec n M mtv m t) mtv
  := by subst p; rfl

noncomputable def r_aux (m : Nat) (c : C m) (i : I m)
   (p_m : HEq m 0) (b : Bool) (p_i : HEq i (I.l b m)) : HEq (r m c i) b :=
  HEq.trans (a := r m c i) (b := @T.rec x___ (fun _ _ => Bool) (i.rec (fun b _ => b) (fun _ => false) : Bool) (x___ + m) (c x___)) (c := b) sorry
    (HEq.trans (a := @T.rec x___ (fun _ _ => Bool) (i.rec (fun b _ => b) (fun _ => false) : Bool) (x___ + m) (c x___))
      (b := (i.rec (fun b _ => b) (fun _ => false) : Bool)) (c := b) 
      (@T.rec_aux x___ (fun _ _ => Bool) (i.rec (fun b _ => b) (fun _ => false)) (x___ + m) (c x___) sorry) sorry)

noncomputable def g_aux (fn : Nat → E) (m : Nat) (c : C m) (i : I m) (n : Nat)
   (p_m : HEq m 0) (b : Bool) (p_i : HEq i (I.l b m)) (p_fn : HEq (fn n) E.b) : HEq (g fn m c i n) b :=
  HEq.trans (a := g fn m c i n) (b := r m c i) (c := b) 
    (HEq.trans (a := g fn m c i n) (b := @T.rec x___ (fun _ _ => Bool) (r m c i) (x___ + m) (c x___)) (c := r m c i) sorry sorry)
    (r_aux m c i sorry b p_i)

noncomputable def f_aux (fn : Nat → E) (m : Nat) (c : C m) (i : I m) (e : E) 
   (p_m : HEq m 0) (b : Bool) (p_i : HEq i (I.l b m)) (n : Nat) (p_e : HEq e (E.a n)) (p_fn : HEq (fn n) E.b) : HEq (f fn (.a m) c i e) b :=
  HEq.trans
    (a := f fn (.a m) c i e)
    (b := m.rec (motive := fun _ => Bool) (g fn m c i n) (fun _ _ => false))
    (c := b) sorry
      (HEq.trans
        (a := m.rec (motive := fun _ => Bool) (g fn m c i n) (fun _ _ => false))
        (b := g fn m c i n)
        (c := b) sorry (@g_aux fn m c i n p_m b p_i sorry))

noncomputable def fpTrans (k : K) (c : C 0) : f fn (.a 0) c (.l true 0) (.a (K.rec 0 k)) = true :=
  L4L.castHEq
    (L4L.appArgHEq' (Eq (f fn (.a 0) c (.l true 0) (.a (K.rec 0 k))))
      (f_aux fn 0 c (.l true 0) (.a (K.rec 0 k)) HEq.rfl true HEq.rfl (K.rec 0 k) HEq.rfl sorry))
    rfl
