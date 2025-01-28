import patch.PatchTheorems
import Lean4Less.Commands

inductive K : Prop where
| mk : K

inductive I : Nat → Type where
| l (n : Nat) : I n
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

noncomputable def r (m : Nat) (c : C m) (i : I m) : I m :=
  @T.rec x___ (fun _ _ => I m) i (x___ + m) (c x___)

@[reducible]
noncomputable def g (fn : Nat → E) (m : Nat) (c : C m) (i : I m) (n : Nat) : I m :=
(fn n).rec
  (fun _ => .r m) -- .a _ => ..
  (@T.rec y___ (fun _ _ => I m) (r m c i) (y___ + m) (c y___)) -- .b => ..
set_option pp.all true in

def F : E → Type
| .a m => (c : C m) → (i : I m) → E → I m
| .b => Bool

noncomputable def f (fn : Nat → E) : (e : E) → F e
| .a m =>
  fun (c : C m) (i : I m) (e : E) => match e with
  | .a n => m.rec (motive := fun _ => I m) (g fn m c i n) (fun _ _ => .r m)
  | .b => .r m
| .b => .true

def fn : Nat → E
| .zero => .b
| _ => .a 0

noncomputable def ex (k : K) : K.rec 0 k = 0 := rfl
-- partial WHNF
noncomputable def fpr (k : K) (c : C 0) : f (fun (n : Nat) => n.rec (.b) (fun _ _ => .a 0)) (.a 0) c (.l 0) (.a (K.rec 0 k)) = r 0 c (.l 0) := rfl
#check_l4l fpr
-- full WHNF
noncomputable def fp (k : K) (c : C 0) : f fn (.a 0) c (.l 0) (.a (K.rec 0 k)) = .l 0 := rfl
#check_l4l fp
-- translation should use the same auxiliary function as `fp`
noncomputable def fp' (c : C 0) : f fn (.a 0) c (.l 0) (.a 0) = .l 0 := rfl


def T.rec_aux {n : Nat}
  {M : (m : Nat) → T n m → Sort u}
    (mtv : M n (T.mk n)) {m : Nat} (t : T n m) (p : n = m) :
      HEq (@T.rec n M mtv m t) mtv
  := by subst p; rfl

noncomputable def r_aux (m : Nat) (c : C m) (i : I m)
   (p_m : HEq m 0) : HEq (r m c i) i :=
  HEq.trans (a := r m c i) (b := @T.rec x___ (fun _ _ => I m) i (x___ + m) (c x___)) (c := i) sorry
    (@T.rec_aux x___ (fun _ _ => I m) i (x___ + m) (c x___) sorry)

noncomputable def g_aux (fn : Nat → E) (m : Nat) (c : C m) (i : I m) (n : Nat)
   (p_m : HEq m 0) (p_fn : HEq (fn n) E.b) : HEq (g fn m c i n) i :=
  HEq.trans (a := g fn m c i n) (b := r m c i) (c := i) 
    (HEq.trans (a := g fn m c i n) (b := @T.rec x___ (fun _ _ => I m) (r m c i) (x___ + m) (c x___)) (c := r m c i) sorry sorry)
    (r_aux m c i sorry)

noncomputable def f_aux (fn : Nat → E) (m : Nat) (c : C m) (i : I m) (e : E) 
   (p_m : HEq m 0) (n : Nat) (p_e : HEq e (E.a n)) (p_fn : HEq (fn n) E.b) : HEq (f fn (.a m) c i e) i :=
  HEq.trans
    (a := f fn (.a m) c i e)
    (b := m.rec (motive := fun _ => I m) (g fn m c i n) (fun _ _ => .r m))
    (c := i) sorry
      (HEq.trans
        (a := m.rec (motive := fun _ => I m) (g fn m c i n) (fun _ _ => .r m))
        (b := g fn m c i n)
        (c := i) sorry (@g_aux fn m c i n p_m sorry))

noncomputable def fpTrans (k : K) (c : C 0) : f fn (.a 0) c (.l 0) (.a (K.rec 0 k)) = .l 0 :=
  L4L.castHEq
    (L4L.appArgHEq' (Eq (f fn (.a 0) c (.l 0) (.a (K.rec 0 k))))
      (f_aux fn 0 c (.l 0) (.a (K.rec 0 k)) HEq.rfl (K.rec 0 k) HEq.rfl sorry))
    rfl
