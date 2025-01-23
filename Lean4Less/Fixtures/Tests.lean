import patch.PatchTheorems
import Lean4Less.Commands

theorem my_eq_of_heq {α : Sort u} {a a' : α} (h : HEq a a') : Eq a a' := eq_of_heq h

universe u v

axiom P : Prop
axiom Q : P → Prop
axiom p : P
axiom q : P
axiom r : P

axiom X : (p : P) → Q p → Q p

def forallEx : Q q → Q q := fun (qp : Q p) => X p qp 

-- def forallEx' : Q q → Q q :=
-- @L4L.castHEq (Q p → Q p) (Q q → Q q)
--   (@L4L.forallHEqAB (Q p) (Q q) (Q p) (Q q) (@L4L.appArgHEq P Prop Q p q (L4L.prfIrrel p q))
--     (@L4L.appArgHEq P Prop Q p q (L4L.prfIrrel p q)))
--   fun (qp : Q p) => X p qp
-- def forallEx'' : Q q → Q q :=
--   fun (qq : Q q) => @L4L.castHEq (Q p) (Q q) (@L4L.appArgHEq P Prop Q p q (L4L.prfIrrel p q))
--                       (X p (@L4L.castHEq (Q q) (Q p) (@L4L.appArgHEq P Prop Q q p (L4L.prfIrrel q p)) qq)) 
-- #check_off forallEx''
-- set_option pp.all true
-- #print Std.Tactic.BVDecide.BVExpr.bitblast.go
-- #check_only Std.Sat.AIG.toCNF.State.addGate

axiom Qp : Q p
axiom Qq : Q q

axiom T : (p : P) → Q p → Prop

axiom t : T p Qp

inductive I : Type where
| left  : P → I
| right : P → I

axiom LL : (x : P) → P → Q x → P → P → P → Q x → Prop
axiom ll : LL p p Qp p p p Qp

-- def absTest : LL q p Qq p p p Qq := ll
axiom N : Nat → (x : P) → Q x → Prop
axiom Np : N 0 p Qp
axiom Nq : N 0 q Qq

def IT : I → Type
| .left x  => P → P → P → P → P → P → (n : Nat) → (Qx : Q x) → N n x Qx → Prop
| .right _ => Bool

axiom M : (i : I) → (j : I) → IT i → IT j
axiom mp : M (.right p) (.left p) true p p p p p p 0 Qp Np
axiom mq : M (.right q) (.left q) true p p p p p p 0 Qq Nq
def absTest : M (.right p) (.left p) true p p p p p p 0 Qp Np := mq
axiom QQ : Nat → P → P → Prop
axiom QQp : QQ 0 p p
axiom QQq : QQ 0 q q

-- theorem appArgHEq' {A : Sort u} {U : A → Sort v}
--   (f : (a : A) → U a)
--   (a b : A) (hab : Eq a b)
--   : HEq (f a) (f b) := sorry

theorem eq_of_heq' {A : Sort u} {a a' : A} (h : HEq a a') : Eq a a' :=
  have (A B : Sort u) (a : A) (b : B) (h₁ : HEq a b) : (h : Eq A B) → Eq (cast h a) b :=
    h₁.rec (fun _ => rfl)
  this A A a a' h rfl

-- #check_l4l eq_of_heq'

namespace Demo
variable (A : P → Nat → Nat → Nat → Nat → Nat → Nat → Prop)

theorem absDemoA (Aq : A q 0 0 0 0 0 0) : A p 0 0 0 0 0 0 := Aq

inductive I : Type where
| left  : P → I
| right : P → I

def IT : I → Type
| .left _  => Unit
| .right _ => Bool

axiom B : (i : I) → Nat → Nat → Nat → IT i → Nat → Nat → Nat → Prop
axiom Bq : B (.left q) 0 0 0 () 0 0 0

theorem absDemoB : B (.left p) 0 0 0 () 0 0 0 := Bq

def ITC : I → Type
| .left _  => Nat → Nat → Nat → Prop
| .right _ => Bool

axiom C : (i : I) → Nat → Nat → Nat → ITC i
axiom Cq : C (.left q) 0 0 0 0 0 0

theorem absDemoC : C (.left p) 0 0 0 0 0 0 := Cq

axiom Q : P → Prop
axiom Qp : Q p
axiom Qq : Q q

def ITD : I → Type
| .left x  => Nat → Q x → Nat → Prop
| .right _ => Bool

axiom D : (i : I) → Nat → Nat → Nat → ITD i
axiom Dq : D (.left q) 0 0 0 0 Qq 0

theorem absDemoD : D (.left p) 0 0 0 0 Qp 0 := Dq

inductive I' : Type where
| left  : P → P → I'
| right : P → P → I'

def IT' : I' → Type
| .left _ _  => Unit
| .right _ _ => Bool

axiom E : (i : I') → Nat → Nat → Nat → IT' i → Nat → Nat → Nat → Prop
axiom Eq : E (.left q q) 0 0 0 () 0 0 0

theorem absDemoE : E (.left p p) 0 0 0 () 0 0 0 := Eq

axiom F : (p : P) → Nat
axiom P : Nat → Prop
axiom Pq : P (F q)
theorem absDemoF : P (F p) := Pq
end Demo

-- def IT : I → Type
-- | .left x  => Q x → P → P → P → P → P → P → Prop
-- | .right _ => Bool
--
-- axiom M : (i : I) → IT i
-- axiom mp : M (.left p) Qp p p p p p p
-- axiom mq : M (.left q) Qq p p p p p p
-- def absTest : M (.left p) Qp p p p p p p := mq
-- def absTest : QQ 0 p p := QQq

-- with proof irrelevance, `t` would suffice
def nestedPrfIrrelTest : T q Qq := t

inductive K : Prop where
| mk : K

namespace auxdefs

inductive X : Nat → Type where
| l (n : Nat) : X n
| r (n : Nat) : X n

inductive E : Type where
| a : E
| b : E

inductive T : Nat → Nat → Prop where
| mk : (n : Nat) → T n n

#print T.rec
/-
T.rec.{u} : {n : Nat} →
  {C : (n' : Nat) → T n n' → Sort u} →
    C n (T.mk n) → {n' : Nat} → (t : T n n') →
      C n' t
-/

def x : Nat := sorry

abbrev C := fun m => (n : Nat) → T n (n + m)

noncomputable def f (m : Nat) (c : C m) (i : X m) : E → X m
| .a => @T.rec x (fun _ _ => X m) i (x + m) (c x)
| .b => .r m

noncomputable def fp (c : C 0) : f 0 c (.l 0) .a = .l 0 := rfl
noncomputable def fpTrans1 (c : C 0) : f 0 c (.l 0) .a = .l 0 :=
  L4L.castHEq
    (L4L.appArgHEq (Eq (f 0 c (.l 0) .a))
      -- proof that `@T.rec x (fun _ _ => E) (.c 0) (x + 0) (c x) = .c 0` by KLR
      -- (i.e., `f 0 c .a = .a`)
      (L4L.appArgHEq (@T.rec _ (fun _ _ => X 0) (.l 0) _) (L4L.prfIrrelHEq (c x) (.mk x))))
    rfl

def T.rec_aux {n : Nat} 
  {M : (m : Nat) → T n m → Sort u} 
    (mtv : M n (T.mk n)) {m : Nat} (t : T n m) (p : n = m) :
      HEq (@T.rec n M mtv m t) mtv
  := by subst p; rfl

noncomputable def f_aux (m : Nat) (c : C m) (e : E) (i : X m) (p_m : HEq m 0) (p_e : HEq e E.a) : HEq (f m c i e) i :=
  -- need to cast WP dependencies
  let c' := @cast (C m) (C 0) sorry c
  let i' := @cast (X m) (X 0) sorry i

  let p := HEq.trans (a := f m c i e) (b := (f 0 c' i' E.a)) (c := i') sorry (@T.rec_aux x (fun _ _ => X 0) i' (m := x) (c' x) (by subst p_m; rfl))

  sorry
--
-- noncomputable def fpTrans2 (n : Nat) (p : n = 0) (c : C n) (i : X n) : f n c i .a = i :=
--   L4L.castHEq
--     (L4L.appArgHEq' (Eq (f n c .a))
--       (f_aux n c .a p rfl))
--     rfl
--
-- def T.rec_aux' {n : Nat} 
--   {M : (m : Nat) → T n m → Sort u} 
--     (mtv : M n (T.mk n)) (t : T n n):
--       HEq (@T.rec n M mtv n t) mtv
--   := by rfl
--
-- noncomputable def f_aux' (c : C 0) : HEq (f 0 c E.a) E.a :=
--   @T.rec_aux' x (fun _ _ => E) .a (c x)
--
-- noncomputable def fpTrans2' (c : C 0) : f 0 c .a = .a :=
--   L4L.castHEq
--     (L4L.appArgHEq' (Eq (f 0 c .a))
--       (f_aux' c))
--     rfl

-- inductive H
-- | l : E → Nat → H
-- | r : H
--
-- noncomputable def g (m : Nat) (c : C m) : H → E
-- | .l e n => @T.rec n (fun _ _ => E) (f m c e) n (T.mk n)
-- | .r => .b
--
-- noncomputable def ug : E := g 0 T.mk (.l .a 0)

end auxdefs

namespace tmp

axiom P : Prop
inductive T : (p : P) → Type where
| mk (p : P) : T p
-- needed so that T isn't a struct (and doesn't use struct-like reduction)
| extra (p : P) : T p

#print T.rec
-- T.rec.{u} {p : P} {motive : tmp.T p → Sort u}
--   (mk : (p_1 : P) → motive (@tmp.T.mk p p_1)) (t : tmp.T p) : motive t

def castEx (p q : P) :
  @T.rec p (fun _ => Bool) true true
    (@cast (T q) (T p) (congrArg T (L4L.prfIrrel q p)) (.mk q))
  = true
   := rfl

-- TODO ask mario about this
-- example {P Q : Prop} (p : P) (q : Q) (h : And P Q) :
--   @And.rec P Q (fun _ => Bool) (fun _ _ => true) (And.intro p q) -- reduces to `true`
--     =
--   @And.rec P Q (fun _ => Bool) (fun _ _ => true) h -- cannot reduce (`And` is not K-like or struct-like)
--   := rfl --fails
axiom h : And P P
#reduce @And.rec P P (fun _ => Bool) (fun _ _ => true) h

example : k = K.mk := rfl
example : @K.rec (fun _ => Bool) true k = @K.rec (fun _ => Bool) true K.mk := rfl
example : @K.rec (fun _ => Bool) true K.mk = true := rfl
-- not OK in Lean-
theorem ex4 : @K.rec (fun _ => Bool) true k = true := rfl
#check_off tmp.ex2

end tmp

-- K.rec.{u}
--   {motive : K → Sort u} 
--   (mk : motive K.mk)
--   (t : K) : motive t
inductive TT : Nat → Type where

def Kex (k : K) (t : TT 0) : TT (@K.rec (fun _ => Nat) 0 k) := t
-- #check_l4l Kex
--
--
theorem my_eq_or_lt_of_le {n m: Nat} (h : LE.le n m) : Or (Eq n m) (LT.lt n m) :=
  match n, h with
  | .zero, _ =>
    match m with
    | .zero => Or.inl rfl
    | .succ _ => Or.inr (Nat.succ_le_succ (Nat.zero_le _))
  | .succ n, h =>
    match m, h with
    | .zero, h => absurd h (Nat.not_succ_le_zero _)
    | .succ m, h => 
      have : LE.le n m := Nat.le_of_succ_le_succ h
      match Nat.eq_or_lt_of_le this with
      | Or.inl h => Or.inl (h ▸ rfl)
      | Or.inr h => Or.inr (Nat.succ_le_succ h)

  -- | zero,   zero,   _ => Or.inl rfl
  -- | zero,   succ _, _ => Or.inr (Nat.succ_le_succ (Nat.zero_le _))
  -- | succ _, zero,   h => absurd h (not_succ_le_zero _)
  -- | succ n, succ m, h =>
  --   have : LE.le n m := Nat.le_of_succ_le_succ h
  --   match Nat.eq_or_lt_of_le this with
  --   | Or.inl h => Or.inl (h ▸ rfl)
  --   | Or.inr h => Or.inr (succ_le_succ h)
variable (x y : Nat) (hxy : x ≤ y)
set_option pp.explicit true in
-- #print Nat.gcd
-- #reduce (proofs := true) my_eq_or_lt_of_le hxy
-- def ktest : (@K.rec (fun _ => Bool) true k) = 

axiom k : K 
axiom k' : K 
axiom BK : Bool → Type
axiom hk : BK (@K.rec (fun _ => Bool) true k)
def KT : Type := (@K.rec (fun _ => Type) (Nat → Prop) k)
axiom Temp : (Nat → KT) → Type
def temp : Type := Temp (fun n m => P)

abbrev gcd (m : @& Nat) : Nat :=
  if let Nat.succ m' := m then
    gcd m'
  else
    0
  termination_by m

-- theorem ex (y : Nat) : gcd (Nat.succ y) = gcd y := rfl
-- #print gcd
-- #check_l4l ex
--
-- axiom x : Nat
-- axiom y : Nat
--
-- #reduce gcd (Nat.succ x)

-- #print PProd
-- set_option pp.explicit true in
-- theorem ex : @WellFounded _
--      (@invImage ((_ : Nat) ×' Nat) Nat (fun x => @PSigma.casesOn Nat (fun m => Nat) (fun _x => Nat) x fun m n => m)
--          (@instWellFoundedRelationOfSizeOf Nat instSizeOfNat)).1 :=
--    (@invImage ((_ : Nat) ×' Nat) Nat (fun x => @PSigma.casesOn Nat (fun m => Nat) (fun _x => Nat) x fun m n => m)
--        (@instWellFoundedRelationOfSizeOf Nat instSizeOfNat)).2
def h1 := forall {α : Type u} {β : α -> Type v} [A : BEq.{u} α] [B : Hashable α] [C : @LawfulBEq α A] {a : α} {c : Nat}, 
  @Eq (Option.{v} (β a)) (@Std.DHashMap.get?.{u, v} α β A B C (@Std.DHashMap.empty.{u, v} α β A B c) a)
    (@Std.DHashMap.get?.{u, v} α β A B C (@Std.DHashMap.empty.{u, v} α β A B c) a)

def h2 := forall {α : Type u} {β : α -> Type v} [A : BEq.{u} α] [B : Hashable α] [C : @LawfulBEq α A] {a : α} {c : Nat}, 
  @Eq (Option.{v} (β a)) (@Std.DHashMap.get?.{u, v} α β A B C (@Std.DHashMap.empty.{u, v} α β A B c) a)
    (@Std.DHashMap.Internal.Raw₀.get?.{u, v} α β A C B (@Std.DHashMap.Internal.Raw₀.empty.{u, v} α β c) a)

-- theorem HashMapTest' {α : Type u} {β : α → Type v} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : @LawfulBEq α inst] {a : α} {c : Nat} :
--   @Eq (Option (β a)) (@Std.DHashMap.get? α β inst inst_1 inst_2 (@Std.DHashMap.empty α β inst inst_1 c) a)
--     (@Std.DHashMap.Internal.Raw₀.get? α β inst inst_2 inst_1 (@Std.DHashMap.Internal.Raw₀.empty α β c) a) :=
--   @L4L.castHEq _ _
--     (@L4L.appArgHEq _ Prop
--       (@Eq _ (@Std.DHashMap.get? α β inst inst_1 inst_2 (@Std.DHashMap.empty α β inst inst_1 c) a)) _ _
--       (@L4L.appArgHEq (Std.DHashMap.Internal.Raw₀ α β) (Option (β a))
--         (fun (m : Std.DHashMap.Internal.Raw₀ α β) => @Std.DHashMap.Internal.Raw₀.get? α β inst inst_2 inst_1 m a)
--         (@Subtype.mk (Std.DHashMap.Raw α β)
--           (fun (m : Std.DHashMap.Raw α β) =>
--             @LT.lt Nat instLTNat 0
--               (@Array.size (Std.DHashMap.Internal.AssocList α β) (@Std.DHashMap.Raw.buckets α β m)))
--           (@Subtype.val (Std.DHashMap.Raw α β)
--             (fun (m : Std.DHashMap.Raw α β) => @Std.DHashMap.Raw.WF α β inst inst_1 m)
--             (@Std.DHashMap.empty α β inst inst_1 c))
--           (@Std.DHashMap.get?.proof_1 α β inst inst_1 (@Std.DHashMap.empty α β inst inst_1 c)))
--         (@Std.DHashMap.Internal.Raw₀.empty α β c)
--         sorry))
--     (@rfl (Option (β a)) (@Std.DHashMap.get? α β inst inst_1 inst_2 (@Std.DHashMap.empty α β inst inst_1 c) a))

axiom tP : Nat → Prop
axiom tempaux : tP 0
set_option pp.all true
-- #check Std.Sat.AIG.denote.go.eq_def
-- -- #check_off eq_of_heq
-- #check_off Std.Sat.AIG.denote.go_eq_of_isPrefix._unary

-- def temp : Q p := X p Qq
-- #print UInt16.ofNat_one


-- def HashMapTest {α : Type u} {β : α → Type v} [BEq α] [Hashable α] [LawfulBEq α] {a : α}
--   {c : Nat} : Std.DHashMap.Internal.Raw₀.get? ⟨(Std.DHashMap.empty c : Std.DHashMap α β).val, sorry⟩ a = Std.DHashMap.Internal.Raw₀.get? (Subtype.mk (Subtype.val (Std.DHashMap.empty c)) (@Std.DHashMap.Internal.Raw₀.empty.proof_1 α β c)) a := rfl
-- #print Nat.succ_le_succ.match_1
-- #check_off Nat.succ_le_succ.match_1

theorem HashMapTest {α : Type u} {β : α → Type v} [BEq α] [Hashable α] [LawfulBEq α] {a : α}
  {c : Nat} : (Std.DHashMap.empty c : Std.DHashMap α β).get? a = (Std.DHashMap.Internal.Raw₀.empty c).get? a := rfl

set_option pp.explicit true
-- #print PProd
-- #print Nat.modCore._unary.proof_1

-- succeeds because of K-like reduction
-- (do not need constructor application to reduce)
noncomputable def kLikeReduction : BK true := hk

axiom A : Type
axiom a : A
axiom h : Eq A A
-- axiom R : BK true → P → Prop
theorem aux (α β : Sort u) (a : α) (b : β) (h₁ : HEq a b) : (h : Eq α β) → Eq (cast h a) b :=
  h₁.rec (fun _ => rfl)
axiom aux' : (α β : Sort u) → (a : α) → (b : β) → HEq a b → (h : Eq α β) → Eq (cast h a) b

def letFun' {α : Sort u} {β : α → Sort v} (v : α) (f : (x : α) → β x) : β v := f v

-- axiom ax' : (@Eq.rec (Type 1) Type (fun (x : Type 1) (x_1 : @Eq (Type 1) Type x) => x) n Type axh)
-- axiom axHEq : HEq axh (@Eq.refl (Type 1) Type)
-- -- axiom ax (α : Sort u) (a : α) : BK (@K.rec (fun _ => Bool) true k)
-- -- axiom ax' (α : Sort u) (a : α) : BK true → (a' : α) → cast (axh α α) a = a'
-- axiom Ty : Type
-- axiom ty : Ty
-- 
-- noncomputable def eq_of_heq' : cast axh n :=
--   ax'
-- -#check_l4l eq_of_heq

axiom n : Type
axiom n' : Type
axiom axh : Type = Type
axiom ax : cast axh n
axiom ax' : n → Prop
-- axiom ax (α : Sort u) (a : α) : BK (@K.rec (fun _ => Bool) true k)
-- axiom ax' (α : Sort u) (a : α) : BK true → (a' : α) → cast (axh α α) a = a'
axiom Ty : Type
axiom ty : Ty
-- noncomputable def eq_of_heq' : Prop :=
--   ax' ax 
-- #check_l4l eq_of_heq'
-- set_option pp.explicit true in
-- #print eq_of_heq'

-- def ex : ∀ x : P, (@dite Prop P (.isTrue x) (fun p => Q p) (fun p => True)) := fun x => Qq

-- #print ex
axiom L : (p : P) → ((q : Q p) → Q p) → Type
axiom l : L q fun qq : Q q => qq

noncomputable def lamTest : L p fun qp : Q p => qp := l
-- #check_l4l lamTest

axiom L' : (P Q : Prop) → ((p : P) → (q : Q) → Type) → Type

axiom M1 : {P : Prop} → P → Type
axiom M2 : {P Q : Prop} → P → Q → Type

axiom l1 : L' (Q q) (Q q) fun _qq qq' : Q q => M1 qq'
axiom l2 : L' (Q q) (Q q) fun qq qq' : Q q => M2 qq qq'
noncomputable def lamTest1 : L' (Q p) (Q q) fun _qp qq => M1 qq := l1
noncomputable def lamTest2 : L' (Q p) (Q q) fun qp qq => M2 qp qq := l2

-- #print Eq.rec
set_option pp.explicit true
-- #print if_pos.match_1
-- #check_only lamTest
-- #check_l4l ex
-- #check_l4l ex
-- #print Fin.mk_zero
-- #check_l4l Fin.mk_zero

-- #check_l4l kLikeReduction
-- axiom T : Type → Type
-- axiom t : T Prop
--
-- unsafe def test : Nat → Type
-- | .zero => Prop
-- | .succ _ => (fun (x : T (test .zero)) => Bool) t
--
-- mutual
--   def test1 : Nat → Type
--   | .zero => Prop
--   | .succ _ => (fun (x : T (test2 .zero)) => Bool) t
--   def test2 : Nat → Type
--   | .zero => Prop
--   | .succ _ => (fun (x : T (test1 .zero)) => Bool) t
-- end

axiom G : P → Prop
inductive H : (p : P) → G p → Type where
| mk (p : P) (g : G p) : H p g

noncomputable def pushTest : (g : G q) → H q g := fun (g : G p) => H.mk p g
#check_l4l pushTest
noncomputable def pushTestIdem : (g : G q) → G q := fun (g : G p) => g
#check_l4l pushTestIdem

axiom Hq : G q → Type
noncomputable def pushTestIdemApp : (g : G q) → Type := fun (g : G p) => Hq g
-- #check_l4l pushTestIdem

-- #print BitVec.mul_def

theorem size_toUTF8 (s : String) : s.toUTF8.size = s.utf8ByteSize := by
  simp [String.toUTF8, ByteArray.size, Array.size, String.utf8ByteSize, List.bind]
  induction s.data <;> simp [List.map, List.join, String.utf8ByteSize.go, Nat.add_comm, *]
-- #print size_toUTF8
-- #check_off size_toUTF8

def F : Bool → Type
| true => Bool
| _ => Unit

structure S : Type where
b : Bool
f : F b

def projTest {B : Bool → Type} (s : B (S.mk true true).2) : B (@K.rec (fun _ => S) (S.mk true true) k).2 := s
-- #check_l4l projTest

-- axiom ex : B (L4L.castHEq.{1} (FS (K.rec.{1} (fun (x._@.Tests._hyg.675 : K) => S) (S.mk Bool.true Bool.true) k)) Bool (L4L.appArgHEq'.{1, 2} S (fun (t : S) => (fun (x : S) => (fun (x._@.Tests._hyg.603.614 : S) => Type) x) t) (S.rec.{2} (fun (x : S) => (fun (x._@.Tests._hyg.603.614 : S) => Type) x) (fun (b : Bool) (f : F b) => (fun (b._@.Tests._hyg.634 : Bool) (f._@.Tests._hyg.635 : F b._@.Tests._hyg.634) => Bool.casesOn.{2} (fun (x : Bool) => forall (f._@.Tests._hyg.635 : F x), (fun (x._@.Tests._hyg.603.614 : S) => Type) (S.mk x f._@.Tests._hyg.635)) b._@.Tests._hyg.634 (fun (f._@.Tests._hyg.635 : F Bool.false) => (fun (x._@.Tests._hyg.631 : S) => Unit) (S.mk Bool.false f._@.Tests._hyg.635)) (fun (f._@.Tests._hyg.635 : F Bool.true) => (fun (f._@.Tests._hyg.625 : F Bool.true) => Bool) f._@.Tests._hyg.635) f._@.Tests._hyg.635) b f)) (K.rec.{1} (fun (x._@.Tests._hyg.675 : K) => S) (S.mk Bool.true Bool.true) k) (S.mk Bool.true Bool.true) (L4L.appArgHEq'.{0, 1} K (fun (t : K) => (fun (x._@.Tests._hyg.675 : K) => S) t) (K.rec.{1} (fun (x._@.Tests._hyg.675 : K) => S) (S.mk Bool.true Bool.true)) k K.mk (L4L.prfIrrel K k K.mk))) (S.prj (K.rec.{1} (fun (x._@.Tests._hyg.675 : K) => S) (S.mk Bool.true Bool.true) k)))

-- #check_l4l projTest
