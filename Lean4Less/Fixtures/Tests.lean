import Lean4Less.Commands
import patch.PatchTheoremsAx

universe u v

axiom P : Prop
axiom Q : P → Prop
axiom p : P
axiom q : P
axiom r : P

axiom X : (p : P) → Q p → Q p

def forallEx : Q q → Q q := fun (qp : Q p) => X p qp 

def forallEx' : Q q → Q q :=
@L4L.castHEq (Q p → Q p) (Q q → Q q)
  (@L4L.forallHEqAB (Q p) (Q q) (Q p) (Q q) (@L4L.appArgHEq P Prop Q p q (L4L.prfIrrel p q))
    (@L4L.appArgHEq P Prop Q p q (L4L.prfIrrel p q)))
  fun (qp : Q p) => X p qp
def forallEx'' : Q q → Q q :=
  fun (qq : Q q) => @L4L.castHEq (Q p) (Q q) (@L4L.appArgHEq P Prop Q p q (L4L.prfIrrel p q))
                      (X p (@L4L.castHEq (Q q) (Q p) (@L4L.appArgHEq P Prop Q q p (L4L.prfIrrel q p)) qq)) 
-- #check_off forallEx''

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
axiom A : P → Nat → Nat → Nat → Nat → Nat → Nat → Prop
axiom Aq : A q 0 0 0 0 0 0

theorem absDemoA : A p 0 0 0 0 0 0 := Aq

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
-- K.rec.{u}
--   {motive : K → Sort u} 
--   (mk : motive K.mk)
--   (t : K) : motive t

axiom k : K 
axiom k' : K 
axiom BK : Bool → Type
axiom hk : BK (@K.rec (fun _ => Bool) true k)

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

theorem HashMapTest' {α : Type u} {β : α → Type v} [inst : BEq α] [inst_1 : Hashable α] [inst_2 : @LawfulBEq α inst] {a : α} {c : Nat} :
  @Eq (Option (β a)) (@Std.DHashMap.get? α β inst inst_1 inst_2 (@Std.DHashMap.empty α β inst inst_1 c) a)
    (@Std.DHashMap.Internal.Raw₀.get? α β inst inst_2 inst_1 (@Std.DHashMap.Internal.Raw₀.empty α β c) a) :=
  @L4L.castHEq _ _
    (@L4L.appArgHEq _ Prop
      (@Eq _ (@Std.DHashMap.get? α β inst inst_1 inst_2 (@Std.DHashMap.empty α β inst inst_1 c) a)) _ _
      (@L4L.appArgHEq (Std.DHashMap.Internal.Raw₀ α β) (Option (β a))
        (fun (m : Std.DHashMap.Internal.Raw₀ α β) => @Std.DHashMap.Internal.Raw₀.get? α β inst inst_2 inst_1 m a)
        (@Subtype.mk (Std.DHashMap.Raw α β)
          (fun (m : Std.DHashMap.Raw α β) =>
            @LT.lt Nat instLTNat 0
              (@Array.size (Std.DHashMap.Internal.AssocList α β) (@Std.DHashMap.Raw.buckets α β m)))
          (@Subtype.val (Std.DHashMap.Raw α β)
            (fun (m : Std.DHashMap.Raw α β) => @Std.DHashMap.Raw.WF α β inst inst_1 m)
            (@Std.DHashMap.empty α β inst inst_1 c))
          (@Std.DHashMap.get?.proof_1 α β inst inst_1 (@Std.DHashMap.empty α β inst inst_1 c)))
        (@Std.DHashMap.Internal.Raw₀.empty α β c)
        sorry))
    (@rfl (Option (β a)) (@Std.DHashMap.get? α β inst inst_1 inst_2 (@Std.DHashMap.empty α β inst inst_1 c) a))

axiom tP : Nat → Prop
axiom tempaux : tP 0
set_option pp.all true
-- #check Std.Sat.AIG.denote.go.eq_def
-- -- #check_off eq_of_heq
-- #check_off Std.Sat.AIG.denote.go_eq_of_isPrefix._unary

def temp : Q p := X p Qq
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

axiom M1 : {P : Prop} → P → Type
axiom M2 : {P Q : Prop} → P → Q → Type

axiom L' : (P Q : Prop) → ((p : P) → (q : Q) → Type) → Type

noncomputable def lamTest : L p fun qp : Q p => qp := l

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
axiom H : (p : P) → G p → Type
axiom H.mk : (p : P) → (g : G p) → H p g
axiom gq : G q
axiom gp : G p

noncomputable def pushTest : (g : G q) → H q g := fun (g : G p) => H.mk p g

-- #print BitVec.mul_def

def F : Bool → Nat → Type
| true, .zero => Bool
| _, _ => Unit

structure S (T : Type u) : Type u where
b : Bool
n : Nat
t : T
f : F b n

theorem size_toUTF8 (s : String) : s.toUTF8.size = s.utf8ByteSize := by
  simp [String.toUTF8, ByteArray.size, Array.size, String.utf8ByteSize, List.bind]
  induction s.data <;> simp [List.map, List.join, String.utf8ByteSize.go, Nat.add_comm, *]
-- #print size_toUTF8
-- #check_off size_toUTF8

axiom B : Bool → Type

axiom s : B (S.mk true .zero () true).4
noncomputable def projTest : B (@K.rec (fun _ => S Unit) (S.mk true .zero () true) k).4 := s

-- axiom ex : B (L4L.castHEq.{1} (FS (K.rec.{1} (fun (x._@.Tests._hyg.675 : K) => S) (S.mk Bool.true Bool.true) k)) Bool (L4L.appArgHEq'.{1, 2} S (fun (t : S) => (fun (x : S) => (fun (x._@.Tests._hyg.603.614 : S) => Type) x) t) (S.rec.{2} (fun (x : S) => (fun (x._@.Tests._hyg.603.614 : S) => Type) x) (fun (b : Bool) (f : F b) => (fun (b._@.Tests._hyg.634 : Bool) (f._@.Tests._hyg.635 : F b._@.Tests._hyg.634) => Bool.casesOn.{2} (fun (x : Bool) => forall (f._@.Tests._hyg.635 : F x), (fun (x._@.Tests._hyg.603.614 : S) => Type) (S.mk x f._@.Tests._hyg.635)) b._@.Tests._hyg.634 (fun (f._@.Tests._hyg.635 : F Bool.false) => (fun (x._@.Tests._hyg.631 : S) => Unit) (S.mk Bool.false f._@.Tests._hyg.635)) (fun (f._@.Tests._hyg.635 : F Bool.true) => (fun (f._@.Tests._hyg.625 : F Bool.true) => Bool) f._@.Tests._hyg.635) f._@.Tests._hyg.635) b f)) (K.rec.{1} (fun (x._@.Tests._hyg.675 : K) => S) (S.mk Bool.true Bool.true) k) (S.mk Bool.true Bool.true) (L4L.appArgHEq'.{0, 1} K (fun (t : K) => (fun (x._@.Tests._hyg.675 : K) => S) t) (K.rec.{1} (fun (x._@.Tests._hyg.675 : K) => S) (S.mk Bool.true Bool.true)) k K.mk (L4L.prfIrrel K k K.mk))) (S.prj (K.rec.{1} (fun (x._@.Tests._hyg.675 : K) => S) (S.mk Bool.true Bool.true) k)))

-- #check_l4l projTest
