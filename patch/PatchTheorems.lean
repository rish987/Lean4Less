import Lean.Data.Name

namespace L4L

inductive Level where
| zero  : Level
| succ  : Level → Level
| max   : Level → Level → Level
| imax  : Level → Level → Level
| param : Nat → Level → Level
| inst  : Level → Level
deriving BEq, Inhabited

def z := Nat.zero
def one := Nat.zero
def two := Nat.succ one
def three := Nat.succ two
def four := Nat.succ three
def five := Nat.succ four

namespace Level

def ctorToNat : Level → Nat
  | zero ..  => Nat.zero
  | param .. => one 
  | succ ..  => two 
  | max ..   => three
  | imax ..  => four
  | inst ..  => five

def normLtAux : Level → Nat → Level → Nat → Bool
  | .succ l₁, k₁, l₂, k₂ => normLtAux l₁ (k₁+one) l₂ k₂
  | l₁, k₁, .succ l₂, k₂ => normLtAux l₁ k₁ l₂ (k₂+one)
  | l₁@(max l₁₁ l₁₂), k₁, l₂@(max l₂₁ l₂₂), k₂ =>
    if l₁ == l₂ then k₁ < k₂
    else if l₁₁ != l₂₁ then normLtAux l₁₁ z l₂₁ z
    else normLtAux l₁₂ z l₂₂ z
  | l₁@(imax l₁₁ l₁₂), k₁, l₂@(imax l₂₁ l₂₂), k₂ =>
    if l₁ == l₂ then k₁ < k₂
    else if l₁₁ != l₂₁ then normLtAux l₁₁ z l₂₁ z
    else normLtAux l₁₂ z l₂₂ z
  | .param n₁ _, k₁, param n₂ _, k₂ => if n₁ == n₂ then k₁ < k₂ else Nat.blt n₁ n₂ -- use `Name.lt` because it is lexicographical
  /-
    We also use `Name.lt` in the following case to make sure universe parameters in a declaration
    are not affected by shifted indices. We used to use `Name.quickLt` which is not stable over shifted indices (the hashcodes change),
    and changes to the elaborator could affect the universe parameters and break code that relies on an explicit order.
    Example: test `tests/lean/343.lean`.
   -/
  | l₁, k₁, l₂, k₂ => if l₁ == l₂ then k₁ < k₂ else ctorToNat l₁ < ctorToNat l₂

/--
  A total order on level expressions that has the following properties
  - `succ l` is an immediate successor of `l`.
  - `zero` is the minimal element.
 This total order is used in the normalization procedure. -/
def normLt (l₁ l₂ : Level) : Bool :=
  normLtAux l₁ z l₂ z

def getOffsetAux : Level → Nat → Nat
  | succ u  , r => getOffsetAux u (Nat.succ r)
  | _,        r => r

def getOffset (lvl : Level) : Nat :=
  getOffsetAux lvl z

def getLevelOffset : Level → Level
  | succ u   => getLevelOffset u
  | u        => u

private def isAlreadyNormalizedCheap : Level → Bool
  | .zero    => true
  | .param _ _ => true
  | .succ u  => isAlreadyNormalizedCheap u
  | _       => false

def isZero : Level → Bool
  | zero   => true
  | _      => false

@[reducible]
def isExplicitSubsumedAux (lvls : Array Level) (maxExplicit : Nat) (i : Nat) : Bool :=
  if h : i < lvls.size then
    let lvl := lvls[i]
    if lvl.getOffset ≥ maxExplicit then true
    else isExplicitSubsumedAux lvls maxExplicit (Nat.succ i)
  else
    false

/- Auxiliary function for `normalize`. See `isExplicitSubsumedAux` -/
@[reducible]
def isExplicitSubsumed (lvls : Array Level) (firstNonExplicit : Nat) : Bool :=
  if firstNonExplicit == z then false
  else
    let max := lvls[firstNonExplicit - one]!.getOffset
    isExplicitSubsumedAux lvls max firstNonExplicit

/-
  Auxiliary function for `normalize`. It assumes `lvls` has been sorted using `normLt`.
  It finds the first position that is not an explicit universe. -/
def skipExplicit (lvls : Array Level) (i : Nat) : Nat :=
  if h : i < lvls.size then
    let lvl := lvls[i]
    if lvl.getLevelOffset.isZero then skipExplicit lvls (Nat.succ i) else i
  else
    i

def levelZero :=
  Level.zero

def mkLevelSucc (u : Level) :=
  Level.succ u

def mkLevelMax (u v : Level) :=
  Level.max u v

def mkLevelIMax (u v : Level) :=
  Level.imax u v

def addOffsetAux : Nat → Level → Level
  | .zero,     u => u
  | .succ n, u => addOffsetAux n (mkLevelSucc u)

def addOffset (u : Level) (n : Nat) : Level :=
  u.addOffsetAux n

def accMax (result : Level) (prev : Level) (offset : Nat) : Level :=
  if result.isZero then prev.addOffset offset
  else mkLevelMax result (prev.addOffset offset)

@[reducible]
def mkMaxAux (lvls : Array Level) (extraK : Nat) (i : Nat) (prev : Level) (prevK : Nat) (result : Level) : Level :=
  if h : i < lvls.size then
    let lvl   := lvls[i]
    let curr  := lvl.getLevelOffset
    let currK := lvl.getOffset
    if curr == prev then
      mkMaxAux lvls extraK (Nat.succ i) curr currK result
    else
      mkMaxAux lvls extraK (Nat.succ i) curr currK (accMax result prev (extraK + prevK))
  else
    accMax result prev (extraK + prevK)

private def mkIMaxAux : Level → Level → Level
  | _,    zero => zero
  | zero, u    => u
  | u₁,   u₂   => if u₁ == u₂ then u₁ else mkLevelIMax u₁ u₂

def isNeverZero : Level → Bool
  | zero         => false
  | param ..     => false
  | succ ..      => true
  | max l₁ l₂    => isNeverZero l₁ || isNeverZero l₂
  | imax _  l₂   => isNeverZero l₂
  | inst l       => isNeverZero l

def size : Level → Nat
| zero         => Nat.zero
| param _ l    => one + l.size
| succ l       => two + l.size
| max l₁ l₂    => three + l₁.size + l₂.size
| imax l₁ l₂   => four + l₁.size + l₂.size
| inst l       => five + l.size

instance : SizeOf Level where
  sizeOf l := l.size

theorem offsetLte (l : Level) : sizeOf (l.getLevelOffset) ≤ sizeOf l := by
  simp only [sizeOf, size, getLevelOffset]
  induction l with
  | zero         =>
    simp only [getLevelOffset]
    omega
  | param _ l    =>
    simp only [getLevelOffset]
    omega
  | succ l ih    =>
    simp only [size, getLevelOffset, size]
    omega
  | max l₁ l₂    =>
    simp only [getLevelOffset]
    omega
  | imax l₁ l₂   =>
    simp only [getLevelOffset]
    omega
  | inst l       =>
    simp only [getLevelOffset]
    omega

mutual
def getMaxArgsAux : Level → Array Level → Array Level
  | max l₁ l₂, lvls => getMaxArgsAux l₂ (getMaxArgsAux l₁ lvls)
  | l,         lvls => lvls.push l

@[reducible]
def normalize (l : Level) : Level :=
  if isAlreadyNormalizedCheap l then l
  else
    let k := l.getOffset
    let u := l.getLevelOffset
    -- have hul : sizeOf u ≤ sizeOf l := by
    --   -- sorry
    --   apply offsetLte
    match u with
    | .max l₁ l₂ =>
      let lvls  := getMaxArgsAux (normalize l₁) #[]
      let lvls  := getMaxArgsAux (normalize l₂) lvls
      let lvls  := lvls.qsort normLt
      let firstNonExplicit := skipExplicit lvls z
      let i := if isExplicitSubsumed lvls firstNonExplicit then firstNonExplicit else firstNonExplicit - one
      let lvl₁  := lvls[i]!
      let prev  := lvl₁.getLevelOffset
      let prevK := lvl₁.getOffset
      mkMaxAux lvls k (i+one) prev prevK levelZero
    | .imax l₁ l₂ =>
      if l₂.isNeverZero then addOffset (normalize (.max l₁ l₂)) k
      else
        let l₁ := normalize l₁
        let l₂ := normalize l₂
        addOffset (mkIMaxAux l₁ l₂) k
    | _ => unreachable!
  decreasing_by
  sorry
  sorry
  sorry
  sorry
  sorry
  -- have : sizeOf l₁ < sizeOf (Level.max l₁ l₂) := by
  --   simp only [sizeOf, size]
  --   omega
  -- omega
  -- have : sizeOf l₂ < sizeOf (Level.max l₁ l₂) := by
  --   simp only [sizeOf, size]
  --   omega
  -- omega
  -- have : sizeOf (Level.max l₁ l₂) < sizeOf (Level.imax l₁ l₂) := by
  --   simp only [sizeOf, size]
  --   omega
  -- omega
  -- have : sizeOf l₁ < sizeOf (Level.imax l₁ l₂) := by
  --   simp only [sizeOf, size]
  --   omega
  -- omega
  -- have : sizeOf l₂ < sizeOf (Level.imax l₁ l₂) := by
  --   simp only [sizeOf, size]
  --   omega
  -- omega
end

end Level

-- #eval Level.normalize (.succ (.max (.param `a .zero) (.param `b .zero)))
-- def test : Level.normalize (.max (.param `a .zero) (.param `b .zero)) = Level.normalize (.max (.param `b .zero) (.param `a .zero)) := rfl

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

-- overrides stdlib's definition of `eq_of_heq`; NOTE: this lemma has been manually translated to Lean⁻
theorem eq_of_heq {A : Sort u} {a b : A} (h : HEq a b) : @Eq A a b :=
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

/- --- --- congruence lemmas --- --- -/

--- forall ---

theorem forallHEqABUV' {A B : Sort u} {U : A → Sort v} {V : B → Sort v}
  (hAB : HEq A B) (hUV : (a : A) → (b : B) → HEq a b → HEq (U a) (V b))
  : HEq ((a : A) → U a) ((b : B) → V b) := by
  subst hAB -- TODO define a macro for this
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
  subst hab
  exact hUV a

theorem forallHEqAB {A B : Sort u} {U : Sort v} (hAB : HEq A B)
  : HEq ((a : A) → U) ((b : B) → U) := by
  apply forallHEqABUV hAB HEq.rfl

--- lambda ---

theorem lambdaHEqABUV' {A B : Sort u} {U : A → Sort v} {V : B → Sort v}
  (f : (a : A) → U a) (g : (b : B) → V b)
  (hAB : HEq A B) (hfg : (a : A) → (b : B) → HEq a b → HEq (f a) (g b))
  : HEq (fun a => f a) (fun b => g b) := by
  subst hAB
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
  subst hab
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

-- (below attempts at getting rid of the `hUV` argument from `appHEqABUV'`)

-- theorem revlambdaHEqUV' {A : Sort u} {U V : A → Sort v}
--   {f : (a : A) → U a} {g : (b : A) → V b}
--   (hfg : HEq (fun a => f a) (fun b => g b))
--   :  (a : A) → HEq (f a) (g a) := by
--     intro x
--     sorry -- darn, can't be proven without appHEqUV'
--
-- theorem appHEqUV' {A : Sort u} {U V : A → Sort v}
--   {f : (a : A) → U a} {g : (b : A) → V b} {a : A} {b : A}
--   (hfg : HEq f g) (hab : HEq a b)
--   : HEq (f a) (g b) := by
--   have : Eq U V := by
--     apply funext
--     intro x
--     exact type_eq_of_heq $ revlambdaHEqUV' hfg x
--   subst this
--   subst hfg
--   subst hab
--   rfl

-- -- if only...
-- axiom forallEta {A : Sort u} {U V : A → Sort v} : ((a : A) → U a) = ((b : A) → V b) → U = V
--
-- theorem appHEqABUV' {A B : Sort u} {U : A → Sort v} {V : B → Sort v}
--   (hAB : HEq A B)
--   {f : (a : A) → U a} {g : (b : B) → V b} {a : A} {b : B}
--   (hfg : HEq f g) (hab : HEq a b)
--   : HEq (f a) (g b) := by
--   subst hAB
--   have : Eq U V := by
--     have := type_eq_of_heq hfg
--     exact forallEta this
--   subst this
--   subst hfg
--   subst hab
--   rfl

theorem appHEqABUV' {A B : Sort u} {U : A → Sort v} {V : B → Sort v}
  (hAB : HEq A B) (hUV : (a : A) → (b : B) → HEq a b → HEq (U a) (V b))
  {f : (a : A) → U a} {g : (b : B) → V b} {a : A} {b : B}
  (hfg : HEq f g) (hab : HEq a b)
  : HEq (f a) (g b) := by
  subst hAB
  have : Eq U V := by
    apply funext
    intro x
    exact eq_of_heq $ hUV x x HEq.rfl
  subst this
  subst hfg
  subst hab
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

theorem prfIrrelHEq {P : Prop} (p q : P) : HEq p q := by
  apply heq_of_eq
  exact prfIrrel _ _

theorem prfIrrelHEqPQ {P Q : Prop} (hPQ : HEq P Q) (p : P) (q : Q) : HEq p q := by
  subst hPQ
  exact prfIrrelHEq _ _

def castHEq {α β : Sort u} (h : HEq α β) (a : α) : β := cast (eq_of_heq h) a

def castOrigHEq {α β : Sort u} (h : HEq α β) (a : α) : HEq (castHEq h a) a := by
  subst h
  rfl

def castOrigHEqSymm {α β : Sort u} (h : HEq α β) (a : α) : HEq a (castHEq h a) := by
  subst h
  rfl

def HEqRefl (_n : Nat) {α : Sort u} (a : α) : HEq a a := HEq.refl a

end L4L
