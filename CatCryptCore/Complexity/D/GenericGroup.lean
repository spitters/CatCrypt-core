/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.RGraphInterp
public import CatCryptCore.Complexity.D.Cost
public import CatCryptCore.Complexity.D.FreeNI

/-!
# Generic group algorithms in D as a free theorem with cost

A term of D whose group is a finite ground type `g` and whose group operations are variables of
its context is a generic algorithm in the sense of Shoup and Maurer: its results on two
representations of the group correspond under the isomorphism, at equal cost. This module derives
the statement from the abstraction theorem of D with cost (`Tm.abstraction_cost`).

The operations are a record `GrpOps` (multiplication, inverse, unit) on the carrier `g.den`; the
group laws play no part. The context `homCtx g` holds the operations, and `isoCtx g` adds an
equality test of group elements. An environment of these contexts (`homEnv`, `isoEnv`) charges
each operation a fixed number of steps (`OpCost`). The base relation `homRel g φ` is the graph
of `φ : g.den → g.den` at `g` and equality at every other finite ground type. When `φ` is a
homomorphism of the operations, the environments of two representations are related
(`homEnv_rel`); when `φ` is moreover injective and `g` is not `bool`, the environments with the
equality test are related (`isoEnv_rel`).

A term that respects `homRel g φ` therefore gives `φ`-related results at equal cost
(`hom_free`, `iso_free`); a term with one input element and one output element commutes with `φ`
(`hom_commute`, `iso_commute`). Respect of `homRel g φ` is the condition that the term treats `g`
as an abstract type. It excludes a literal of `g` other than a fixed point of `φ`, a sample, read
or receipt of an element of `g` other than a fixed point, a primitive operation on `g` that does
not commute with `φ` (for instance `wadd` when `g` is a word type), and a branch, write or query
at an element of `g`, since these must be related only when equal. An equality test of group
elements is available only as the operation of `isoCtx`, whose relation holds for injective `φ`;
for a homomorphism that is not injective the theorems hold over `homCtx`, without the test.

The concrete instance is square-and-multiply exponentiation by a list of bits, most significant
first (`powT`). Its evaluation is the power after `n · (m + 4) + w · (m + 1)` steps for `n` bits
of weight `w` and multiplication cost `m` (`powT_eval`): `n + w` multiplications. The term
respects `homRel g φ` (`powT_respB`), so its result commutes with every homomorphism at equal
cost (`powT_commute`).

## Main definitions

* `GrpOps`, `GrpOps.IsHom`, `GrpOps.ofGroup` — group operations and their homomorphisms;
* `homCtx`, `isoCtx`, `OpCost`, `homEnv`, `isoEnv` — the operations as a context of D;
* `homRel` — the graph of a map at the group and equality elsewhere;
* `powStep`, `powT`, `powSpec` — square-and-multiply exponentiation.

## Main results

* `homEnv_rel`, `isoEnv_rel` — the operations of two representations are related;
* `hom_free`, `iso_free` — related results at equal cost for every respecting term;
* `hom_commute`, `iso_commute` — a respecting term commutes with a homomorphism or an
  injective homomorphism, at equal cost;
* `GrpOps.isHom_ofGroup` — a monoid homomorphism of groups is a homomorphism of operations;
* `powT_eval`, `powT_cost`, `powT_respB`, `powT_commute` — exponentiation: its value, its
  number of steps and its commutation with homomorphisms.

## References

* J. C. Reynolds, *Types, abstraction and parametric polymorphism*, IFIP Congress 1983;
* V. Shoup, *Lower bounds for discrete logarithms and related problems*, EUROCRYPT 1997;
* U. Maurer, *Abstract models of computation in cryptography*, IMA Cryptography and Coding 2005.

Search words: generic group model, generic algorithm, representation independence, free theorem,
abstraction theorem, group operation count, square-and-multiply.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D

namespace GenericGroup

/-! ## Group operations and their homomorphisms -/

/-- The operations of a group on a carrier `X`: multiplication, inverse and unit. -/
structure GrpOps (X : Type) where
  /-- The multiplication. -/
  mul : X → X → X
  /-- The inverse. -/
  inv : X → X
  /-- The unit. -/
  one : X

/-- The operations of a group structure. -/
def GrpOps.ofGroup (X : Type) [Group X] : GrpOps X := ⟨(· * ·), (·⁻¹), 1⟩

/-- A homomorphism of group operations: a map that commutes with multiplication, inverse and
unit. -/
structure GrpOps.IsHom {X Y : Type} (M : GrpOps X) (N : GrpOps Y) (φ : X → Y) : Prop where
  /-- The map commutes with multiplication. -/
  map_mul : ∀ a b, φ (M.mul a b) = N.mul (φ a) (φ b)
  /-- The map commutes with the inverse. -/
  map_inv : ∀ a, φ (M.inv a) = N.inv (φ a)
  /-- The map sends the unit to the unit. -/
  map_one : φ M.one = N.one

/-- A monoid homomorphism of groups is a homomorphism of their group operations. -/
theorem GrpOps.isHom_ofGroup {X Y : Type} [Group X] [Group Y] (φ : X →* Y) :
    (GrpOps.ofGroup X).IsHom (GrpOps.ofGroup Y) φ :=
  ⟨φ.map_mul, map_inv φ, φ.map_one⟩

/-! ## The operations as a context of D -/

/-- The type of D of the group elements: the finite ground type `g`. -/
abbrev el (g : FTy) : Ty := .base g

/-- The context of the group operations at the carrier `g`: multiplication, inverse and unit,
innermost first. -/
abbrev homCtx (g : FTy) : List Ty := [.arr (.prod (el g) (el g)) (el g), .arr (el g) (el g), el g]

/-- The context of the group operations with an equality test of group elements, innermost. -/
abbrev isoCtx (g : FTy) : List Ty := .arr (.prod (el g) (el g)) .bool :: homCtx g

/-- The steps charged to each group operation. -/
structure OpCost where
  /-- The steps of a multiplication. -/
  mul : ℕ
  /-- The steps of an inverse. -/
  inv : ℕ
  /-- The steps of an equality test. -/
  eq : ℕ

/-- A value after `k` steps. -/
def opT {α : Type} (k : ℕ) (a : α) : CTree α := stepN CTree.tick k (.ret a)

/-- The environment of the group operations `M` at the costs `c`. -/
def homEnv (g : FTy) (M : GrpOps g.den) (c : OpCost) : Env (homCtx g) :=
  Env.cons (τ := .arr (.prod (el g) (el g)) (el g))
    (fun p : g.den × g.den => opT c.mul (M.mul p.1 p.2))
    (Env.cons (τ := .arr (el g) (el g)) (fun a : g.den => opT c.inv (M.inv a))
      (Env.cons (τ := el g) M.one Env.nil))

/-- The equality test of group elements at `k` steps. -/
def eqOp (g : FTy) (k : ℕ) : Val (.arr (.prod (el g) (el g)) .bool) :=
  fun p : g.den × g.den => opT k (@decide (p.1 = p.2) (g.decEq p.1 p.2))

/-- The environment of the group operations `M` and the equality test at the costs `c`. -/
def isoEnv (g : FTy) (M : GrpOps g.den) (c : OpCost) : Env (isoCtx g) :=
  Env.cons (eqOp g c.eq) (homEnv g M c)

/-- The environment of the group operations `M` at the costs `c` with the input element `x`. -/
def homEnv₁ (g : FTy) (M : GrpOps g.den) (c : OpCost) (x : g.den) : Env (el g :: homCtx g) :=
  Env.cons (τ := el g) x (homEnv g M c)

/-- The environment of the group operations `M` and the equality test at the costs `c` with the
input element `x`. -/
def isoEnv₁ (g : FTy) (M : GrpOps g.den) (c : OpCost) (x : g.den) : Env (el g :: isoCtx g) :=
  Env.cons (τ := el g) x (isoEnv g M c)

/-! ## The base relation of a map of the group -/

/-- The graph of `φ` at the group `g` and equality at every other finite ground type. -/
def homRel (g : FTy) (φ : g.den → g.den) : BRel := fun f a b =>
  if h : f = g then φ (cast (congrArg FTy.den h) a) = cast (congrArg FTy.den h) b else a = b

variable {g : FTy} {φ : g.den → g.den}

/-- At the group, the base relation is the graph of `φ`. -/
theorem homRel_self {a b : g.den} : homRel g φ g a b ↔ φ a = b := by
  simp [homRel]

/-- Away from the group, the base relation is equality. -/
theorem homRel_of_ne {f : FTy} (hf : f ≠ g) {a b : f.den} : homRel g φ f a b ↔ a = b := by
  simp [homRel, hf]

/-! ## The free theorem -/

variable {M N : GrpOps g.den}

/-- The operations of two representations are related by the graph of a homomorphism. -/
theorem homEnv_rel (hφ : M.IsHom N φ) (c : OpCost) :
    EnvRelB (homRel g φ) (homEnv g M c) (homEnv g N c) := by
  intro τ x
  cases x with
  | here =>
    intro (u : g.den × g.den) (v : g.den × g.den) huv
    obtain ⟨h1, h2⟩ := huv
    have e1 : φ u.1 = v.1 := homRel_self.1 h1
    have e2 : φ u.2 = v.2 := homRel_self.1 h2
    exact stepN_lift (.ret (homRel_self.2 (show φ (M.mul u.1 u.2) = N.mul v.1 v.2 by
      rw [hφ.map_mul, e1, e2]))) _
  | there x =>
    cases x with
    | here =>
      intro (u : g.den) (v : g.den) huv
      have e : φ u = v := homRel_self.1 huv
      exact stepN_lift (.ret (homRel_self.2 (show φ (M.inv u) = N.inv v by
        rw [hφ.map_inv, e]))) _
    | there x =>
      cases x with
      | here => exact homRel_self.2 hφ.map_one
      | there x => cases x

/-- The operations and equality tests of two representations are related by the graph of an
injective homomorphism, when the group is not `bool`. -/
theorem isoEnv_rel (hφ : M.IsHom N φ) (hinj : Function.Injective φ) (hg : FTy.bool ≠ g)
    (c : OpCost) : EnvRelB (homRel g φ) (isoEnv g M c) (isoEnv g N c) := by
  refine EnvRelB.cons (homEnv_rel hφ c) ?_
  intro (u : g.den × g.den) (v : g.den × g.den) huv
  obtain ⟨h1, h2⟩ := huv
  have e1 : φ u.1 = v.1 := homRel_self.1 h1
  have e2 : φ u.2 = v.2 := homRel_self.1 h2
  refine stepN_lift (.ret ((homRel_of_ne hg).2 (show
    @decide (u.1 = u.2) (g.decEq u.1 u.2) = @decide (v.1 = v.2) (g.decEq v.1 v.2) from ?_))) _
  rw [← e1, ← e2]
  exact decide_eq_decide.2 hinj.eq_iff.symm

/-- The free theorem of a generic group algorithm: a term over the group operations that
respects the graph of a homomorphism `φ` gives `φ`-related results at equal cost on the two
representations. -/
theorem hom_free (hφ : M.IsHom N φ) (c : OpCost) {τ : Ty} (t : Tm (homCtx g) τ)
    (ht : t.RespB (homRel g φ)) :
    CTree.Lift (Ty.relB (homRel g φ) τ) (t.eval (homEnv g M c)) (t.eval (homEnv g N c)) ∧
      (t.eval (homEnv g M c)).cost = (t.eval (homEnv g N c)).cost :=
  t.abstraction_cost ht (homEnv_rel hφ c)

/-- The free theorem of a generic group algorithm with equality tests: a term over the group
operations and the equality test that respects the graph of an injective homomorphism `φ` gives
`φ`-related results at equal cost on the two representations. -/
theorem iso_free (hφ : M.IsHom N φ) (hinj : Function.Injective φ) (hg : FTy.bool ≠ g)
    (c : OpCost) {τ : Ty} (t : Tm (isoCtx g) τ) (ht : t.RespB (homRel g φ)) :
    CTree.Lift (Ty.relB (homRel g φ) τ) (t.eval (isoEnv g M c)) (t.eval (isoEnv g N c)) ∧
      (t.eval (isoEnv g M c)).cost = (t.eval (isoEnv g N c)).cost :=
  t.abstraction_cost ht (isoEnv_rel hφ hinj hg c)

/-- A generic group algorithm with an input element commutes with a homomorphism: on the input
`φ x` over the operations `N` it returns, at equal cost and through the same effects, the image
under `φ` of its result on `x` over the operations `M`. -/
theorem hom_commute (hφ : M.IsHom N φ) (c : OpCost) (t : Tm (el g :: homCtx g) (el g))
    (ht : t.RespB (homRel g φ)) (x : g.den) :
    CTree.Lift (fun a b => φ a = b) (t.eval (homEnv₁ g M c x)) (t.eval (homEnv₁ g N c (φ x))) ∧
      (t.eval (homEnv₁ g M c x)).cost = (t.eval (homEnv₁ g N c (φ x))).cost := by
  have h := t.abstraction_cost ht (ρ := homEnv₁ g M c x) (δ := homEnv₁ g N c (φ x))
    ((homEnv_rel hφ c).cons (τ := el g) (u := x) (v := φ x) (homRel_self.2 rfl))
  exact ⟨CTree.Lift.mono (fun _ _ hab => homRel_self.1 hab) h.1, h.2⟩

/-- A generic group algorithm with an input element and equality tests commutes with an
injective homomorphism, at equal cost and through the same effects. -/
theorem iso_commute (hφ : M.IsHom N φ) (hinj : Function.Injective φ) (hg : FTy.bool ≠ g)
    (c : OpCost) (t : Tm (el g :: isoCtx g) (el g)) (ht : t.RespB (homRel g φ)) (x : g.den) :
    CTree.Lift (fun a b => φ a = b) (t.eval (isoEnv₁ g M c x)) (t.eval (isoEnv₁ g N c (φ x))) ∧
      (t.eval (isoEnv₁ g M c x)).cost = (t.eval (isoEnv₁ g N c (φ x))).cost := by
  have h := t.abstraction_cost ht (ρ := isoEnv₁ g M c x) (δ := isoEnv₁ g N c (φ x))
    ((isoEnv_rel hφ hinj hg c).cons (τ := el g) (u := x) (v := φ x) (homRel_self.2 rfl))
  exact ⟨CTree.Lift.mono (fun _ _ hab => homRel_self.1 hab) h.1, h.2⟩

/-! ## Square-and-multiply exponentiation -/

/-- The step of square-and-multiply on an accumulator and a bit: square, then multiply by the
base when the bit is set. The context holds the pair, the bits, the base and the group
operations. -/
def powStep (g : FTy) : Tm (.prod (el g) .bool :: .list .bool :: el g :: homCtx g) (el g) :=
  .letE (.app (.var (.there (.there (.there .here))))
      (.pair (.fst (.var .here)) (.fst (.var .here))))
    (.ite (.snd (.var (.there .here)))
      (.app (.var (.there (.there (.there (.there .here)))))
        (.pair (.var .here) (.var (.there (.there (.there .here))))))
      (.var .here))

/-- Square-and-multiply exponentiation of the base by a list of bits, most significant first,
as a term over the bits, the base and the group operations. -/
def powT (g : FTy) : Tm (.list .bool :: el g :: homCtx g) (el g) :=
  .foldl (.lam (powStep g)) (.var (.there (.there (.there (.there .here))))) (.var .here)

/-- The power computed by square-and-multiply over the operations `M`. -/
def powSpec (M : GrpOps g.den) (x : g.den) (bits : List Bool) : g.den :=
  bits.foldl (fun acc b => bif b then M.mul (M.mul acc acc) x else M.mul acc acc) M.one

private theorem stepN_stepN {α : Type} (m k : ℕ) (t : CTree α) :
    stepN CTree.tick m (stepN CTree.tick k t) = stepN CTree.tick (m + k) t := by
  induction m with
  | zero => simp [stepN]
  | succ m ih => rw [Nat.add_right_comm]; exact congrArg CTree.tick ih

/-- The environment of square-and-multiply: the bits, the base and the group operations. -/
def powEnv (g : FTy) (M : GrpOps g.den) (c : OpCost) (x : g.den) (bits : List Bool) :
    Env (.list .bool :: el g :: homCtx g) :=
  Env.cons (τ := .list .bool) bits (homEnv₁ g M c x)

/-- One step of square-and-multiply: the next accumulator after `m + 3` steps, and `m + 1` more
when the bit is set. -/
theorem powStep_eval (c : OpCost) (x : g.den) (bits : List Bool) (acc : g.den) (b : Bool) :
    (powStep g).eval (Env.cons (τ := .prod (el g) .bool) (acc, b) (powEnv g M c x bits)) =
      stepN CTree.tick (c.mul + 3 + bif b then c.mul + 1 else 0)
        (CTree.ret (α := Val (el g)) (bif b then M.mul (M.mul acc acc) x else M.mul acc acc)) := by
  cases b
  · change (CTree.tick (stepN CTree.tick c.mul (.ret (M.mul acc acc)))).bind
        (fun v => CTree.tick (CTree.tick (.ret v))) = _
    rw [CTree.bind_tick, stepN_tick_bind, CTree.bind_ret,
      show c.mul + 3 + (bif false then c.mul + 1 else 0) = 1 + (c.mul + 2) by
        simp only [Bool.cond_false]; omega,
      ← stepN_stepN, ← stepN_stepN]
    rfl
  · change (CTree.tick (stepN CTree.tick c.mul (.ret (M.mul acc acc)))).bind
        (fun v => CTree.tick (CTree.tick (CTree.tick
          (stepN CTree.tick c.mul (.ret (M.mul v x)))))) = _
    rw [CTree.bind_tick, stepN_tick_bind, CTree.bind_ret,
      show c.mul + 3 + (bif true then c.mul + 1 else 0) = 1 + (c.mul + (3 + c.mul)) by
        simp only [Bool.cond_true]; omega,
      ← stepN_stepN, ← stepN_stepN, ← stepN_stepN]
    rfl

/-- The fold of square-and-multiply from an accumulator. -/
theorem powT_foldT (c : OpCost) (x : g.den) (bits : List Bool) :
    ∀ (l : List Bool) (acc : g.den),
      foldT CTree.tick (a := .bool) (c := el g)
          (fun v => (powStep g).eval (Env.cons v (powEnv g M c x bits))) acc l =
        stepN CTree.tick (l.length * (c.mul + 4) + l.count true * (c.mul + 1))
          (.ret (l.foldl (fun acc b => bif b then M.mul (M.mul acc acc) x else M.mul acc acc)
            acc)) := by
  intro l
  induction l with
  | nil =>
    intro acc
    rw [List.length_nil, List.count_nil, Nat.zero_mul, Nat.zero_mul]
    rfl
  | cons b l ih =>
    intro acc
    change (CTree.tick ((powStep g).eval
      (Env.cons (τ := .prod (el g) .bool) (acc, b) (powEnv g M c x bits)))).bind _ = _
    rw [powStep_eval, CTree.bind_tick, stepN_tick_bind, CTree.bind_ret]
    erw [ih, stepN_stepN]
    have hT : (b :: l).length * (c.mul + 4) + (b :: l).count true * (c.mul + 1) =
        (c.mul + 3 + bif b then c.mul + 1 else 0) +
          (l.length * (c.mul + 4) + l.count true * (c.mul + 1)) + 1 := by
      cases b <;> simp <;> ring
    rw [hT]
    rfl

/-- Square-and-multiply returns the power after `n · (m + 4) + w · (m + 1)` steps, for `n` bits of
weight `w` and multiplication cost `m`. -/
theorem powT_eval (c : OpCost) (x : g.den) (bits : List Bool) :
    (powT g).eval (powEnv g M c x bits) =
      stepN CTree.tick (bits.length * (c.mul + 4) + bits.count true * (c.mul + 1))
        (.ret (powSpec M x bits)) :=
  powT_foldT c x bits bits M.one

/-- The number of steps of square-and-multiply. -/
theorem powT_cost (c : OpCost) (x : g.den) (bits : List Bool) :
    ((powT g).eval (powEnv g M c x bits)).cost =
      bits.length * (c.mul + 4) + bits.count true * (c.mul + 1) := by
  rw [powT_eval]
  exact (cost_stepN_tick (α := g.den) _ _).trans (Nat.add_zero _)

/-- Square-and-multiply treats the group as an abstract type: it respects the graph of every map
of a group other than `bool`. -/
theorem powT_respB (hg : FTy.bool ≠ g) : (powT g).RespB (homRel g φ) := by
  simp only [powT, powStep, Tm.RespB, and_true, true_and]
  exact fun _ _ h => (homRel_of_ne hg).1 h

/-- Square-and-multiply commutes with every homomorphism of a group other than `bool`, at equal
cost: on the base `φ x` over the operations `N`, it returns the image under `φ` of its result on
`x` over the operations `M`. -/
theorem powT_commute (hφ : M.IsHom N φ) (hg : FTy.bool ≠ g) (c : OpCost) (x : g.den)
    (bits : List Bool) :
    CTree.Lift (fun a b => φ a = b) ((powT g).eval (powEnv g M c x bits))
        ((powT g).eval (powEnv g N c (φ x) bits)) ∧
      ((powT g).eval (powEnv g M c x bits)).cost =
        ((powT g).eval (powEnv g N c (φ x) bits)).cost := by
  have hb : Ty.relB (homRel g φ) (.list .bool) bits bits :=
    List.forall₂_same.2 fun b _ => (homRel_of_ne hg).2 rfl
  have hx : EnvRelB (homRel g φ) (homEnv₁ g M c x) (homEnv₁ g N c (φ x)) :=
    (homEnv_rel hφ c).cons (τ := el g) (u := x) (v := φ x) (homRel_self.2 rfl)
  have h := (powT g).abstraction_cost (powT_respB hg) (ρ := powEnv g M c x bits)
    (δ := powEnv g N c (φ x) bits) (hx.cons (τ := .list .bool) (u := bits) (v := bits) hb)
  exact ⟨CTree.Lift.mono (fun _ _ hab => homRel_self.1 hab) h.1, h.2⟩

end GenericGroup

end CatCrypt.Complexity.D
