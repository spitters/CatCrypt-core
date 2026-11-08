/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.DNBang
public import CatCryptCore.Container.DNCert
public import Mathlib.Data.Matrix.Mul

/-!
# The graded exponential and count matrices of the Diller–Nahm category

The exponential `bangLE n P` at a grade `n : ℕ∞` has the shapes of `P` and, at a shape, the
finite multisets of at most `n` positions of `P` as positions: the exponential `!ₙ` of bounded
linear logic (Girard, Scedrov and Scott, *Bounded linear logic*, TCS 97, 1992). With the counit
at grade `1`, the comultiplication at grade `m * n`, weakening at grade `0` and contraction at
grade `m + n` it is a graded linear exponential comonad on lenses in the sense of Katsumata
(*A double category theoretic analysis of graded linear exponential comonads*, FoSSaCS 2018), the
semantics of the coeffect calculi of Brunel, Gaboardi, Mazza and Zdancewic (*A core quantitative
coeffect calculus*, ESOP 2014) and Ghica and Smith (*Bounded linear types in a resource
semiring*, ESOP 2014). The grades are related by the inclusions `bangLE.sub`.

A Diller–Nahm morphism has grade `n` when each position of its target demands at most `n a`
positions of its source (`DNLens.UsesLE`); grades multiply along composition. At finite
positions the count matrix of a morphism at a shape records the multiplicity of each source
position in the demand of each target position; composition is the matrix product
(`DNLens.countMat_comp`) and a price is the linear map of the matrix (`DNLens.price_eq_mulVec`).

The certificates of `CatCrypt.Container.DillerNahm` are instances. A costed function with use
counts has the upper triangular count matrix `[[n, c], [0, 1]]` (`clockMat`), and the composition
law `n₂ * n₁`, `c₂ + n₂ * c₁` is the product of these matrices; a costed function with a cost
vector has the matrix `[[1, c], [0, 1]]` over `Option ι` (`vecMat`), whose product adds the
costs; the use bound of an interpreted tree is the vector–matrix product of the use bound of the
tree and the use matrix of the handler. The laws of the weighted exponential `bangW S` at a
commutative semiring `S` make it a comonad on lenses when `S` lives in the universe of positions.

## Main definitions

* `bangLE`, `bangLE.map`, `bangLE.sub`, `bangLE.ofBang`, `bangLE.counit`, `bangLE.comult`,
  `bangLE.weak`, `bangLE.contr`, `bangLE.topEquiv` — the graded exponential and its structure;
* `DNLens.UsesLE` — the dependent grade of a Diller–Nahm morphism;
* `DNLens.countMat` — the count matrix at a shape;
* `clockMat`, `vecMat` — the count matrices of `Clocked` and `VecCosted` certificates;
* `bangWFunctor`, `bangWComonad` — the weighted exponential as a comonad on lenses.

## Main results

* `bangLE.counit_comult`, `bangLE.map_counit_comult`, `bangLE.comult_coassoc`,
  `bangLE.contr_comm`, `bangLE.contr_assoc`, `bangLE.contr_weak_left`, `bangLE.contr_weak_right`
  and the naturality statements — the graded comonad and graded comonoid laws;
* `DNLens.UsesLE.comp`, `DNLens.usesLE_const_iff` — grades multiply along composition, and a
  morphism of constant grade `n` is a lens out of `bangLE n`;
* `DNLens.countMat_comp`, `DNLens.countMat_id`, `DNLens.price_eq_mulVec`;
* `clockMat_mul`, `Clocked.countMat_toDN`, `Clocked.toDN_comp_of_countMat`,
  `clockBack_bind_of_countMat`, `vecMat_mul`, `VecCosted.toDN_comp_of_countMat`,
  `useBound_liftM_vecMul` — the composition laws of the certificates as matrix products;
* `bangWMap_id`, `bangWMap_comp`, `bangWCounit_comult`, `bangWMap_counit_comult`,
  `bangWComult_coassoc` — the comonad laws of the weighted exponential.

Search words: graded exponential, bounded linear logic, graded comonad, coeffect, resource
semiring, use count, count matrix, affine monoid, Diller–Nahm, Dialectica, weighted exponential.
-/

set_option autoImplicit false

@[expose] public section

universe u v w u₁ v₁ u₂ v₂ u₃ v₃ uA uA₂ uB

namespace CatCrypt.Container

open PFunctor CategoryTheory
open scoped BigOperators

/-! ## Sizes and counts of a bind -/

/-- The size of a bind is at most the size of the multiset times a bound on the sizes of the
multisets it binds. -/
theorem card_bind_le {α : Type u} {β : Type v} {s : Multiset α} {k : α → Multiset β} {n : ℕ∞}
    (h : ∀ x ∈ s, ((k x).card : ℕ∞) ≤ n) : ((s.bind k).card : ℕ∞) ≤ s.card * n := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    have hx := h x (Multiset.mem_cons_self x s)
    have hs := ih fun y hy => h y (Multiset.mem_cons_of_mem hy)
    simp only [Multiset.cons_bind, Multiset.card_add, Multiset.card_cons, Nat.cast_add,
      Nat.cast_one, add_mul, one_mul]
    rw [add_comm ((s.card : ℕ∞) * n)]
    exact add_le_add hx hs

/-- The sum of a function over a multiset of elements of a finite type is the sum over the type
weighted by the multiplicities. -/
theorem multiset_sum_map_eq_sum_count {β : Type v} {M : Type w} [Fintype β] [DecidableEq β]
    [AddCommMonoid M] (s : Multiset β) (f : β → M) :
    (s.map f).sum = ∑ y, s.count y • f y := by
  rw [Finset.sum_multiset_map_count]
  exact Finset.sum_subset (Finset.subset_univ _) fun y _ hy => by
    simp [Multiset.count_eq_zero.2 (by simpa using hy)]

/-- The multiplicity of `x` in a bind is the sum over the elements `y` of their multiplicity
times the multiplicity of `x` in the multiset bound to `y`. -/
theorem count_bind_eq_sum {α : Type u} {β : Type v} [Fintype β] [DecidableEq β] [DecidableEq α]
    (s : Multiset β) (k : β → Multiset α) (x : α) :
    (s.bind k).count x = ∑ y, s.count y * (k y).count x := by
  rw [Multiset.count_bind, multiset_sum_map_eq_sum_count]
  simp [smul_eq_mul]

/-! ## The graded exponential -/

/-- The exponential at grade `n`: the shapes of `P`, and at a shape the finite multisets of at most
`n` positions of `P` at it. -/
abbrev bangLE (n : ℕ∞) (P : PFunctor.{u, v}) : PFunctor.{u, v} :=
  ⟨P.A, fun a => {m : Multiset (P.B a) // (m.card : ℕ∞) ≤ n}⟩

namespace bangLE

variable {P : PFunctor.{u₁, v₁}} {Q : PFunctor.{u₂, v₂}} {R : PFunctor.{u₃, v₃}}

/-- The action of the graded exponential on a lens: the backward map acts on each element. -/
def map (n : ℕ∞) (l : Lens P Q) : Lens (bangLE n P) (bangLE n Q) where
  toFunA := l.toFunA
  toFunB a m := ⟨m.1.map (l.toFunB a), by simpa using m.2⟩

/-- The inclusion of grades: a multiset of at most `n` positions has at most `m ≥ n`. -/
def sub {m n : ℕ∞} (h : n ≤ m) (P : PFunctor.{u, v}) : Lens (bangLE m P) (bangLE n P) where
  toFunA a := a
  toFunB _ s := ⟨s.1, s.2.trans h⟩

/-- The ungraded exponential over the graded one: a bounded multiset is a multiset. -/
def ofBang (n : ℕ∞) (P : PFunctor.{u, v}) : Lens (bang P) (bangLE n P) where
  toFunA a := a
  toFunB _ s := s.1

/-- The counit at grade `1` (dereliction): a position demands itself once. -/
def counit (P : PFunctor.{u, v}) : Lens (bangLE 1 P) P where
  toFunA a := a
  toFunB _ y := ⟨{y}, by simp⟩

/-- The comultiplication at grade `m * n` (digging): at most `m` multisets of at most `n`
positions demand their sum. -/
def comult (m n : ℕ∞) (P : PFunctor.{u, v}) : Lens (bangLE (m * n) P) (bangLE m (bangLE n P)) where
  toFunA a := a
  toFunB _ M := ⟨M.1.bind Subtype.val,
    (card_bind_le fun x _ => x.2).trans (mul_le_mul' M.2 le_rfl)⟩

/-- Weakening at grade `0`: no position is demanded. -/
def weak (P : PFunctor.{u, v}) : Lens (bangLE 0 P) y.{u, v} where
  toFunA _ := PUnit.unit
  toFunB _ _ := ⟨0, by simp⟩

/-- Contraction at grade `m + n`: a shape is duplicated, and a pair of multisets demands their
sum. -/
def contr (m n : ℕ∞) (P : PFunctor.{u, v}) : Lens (bangLE (m + n) P) (bangLE m P ⊗ bangLE n P) where
  toFunA a := (a, a)
  toFunB _ s := ⟨s.1.1 + s.2.1, by simpa using add_le_add s.1.2 s.2.2⟩

/-- The graded exponential at grade `⊤` is the exponential. -/
def topEquiv (P : PFunctor.{u, v}) : bangLE ⊤ P ≃ₗ bang P where
  toLens := Lens.mk id fun _ s => ⟨s, le_top⟩
  invLens := ofBang ⊤ P
  left_inv := lens_mk_congr fun _ _ => rfl
  right_inv := lens_mk_congr fun _ _ => rfl

/-! ### Functoriality and the inclusions of grades -/

/-- The graded exponential preserves identities. -/
theorem map_id (n : ℕ∞) : map n (Lens.id P) = Lens.id (bangLE n P) :=
  lens_mk_congr fun _ s => Subtype.ext (Multiset.map_id s.1)

/-- The graded exponential preserves composition. -/
theorem map_comp (n : ℕ∞) (m : Lens Q R) (l : Lens P Q) :
    map n (Lens.comp m l) = Lens.comp (map n m) (map n l) :=
  lens_mk_congr fun a s => Subtype.ext (by simp [map, Lens.comp, Function.comp_def])

/-- The inclusion of a grade in itself is the identity. -/
theorem sub_refl (n : ℕ∞) (P : PFunctor.{u, v}) : sub (le_refl n) P = Lens.id (bangLE n P) :=
  lens_mk_congr fun _ _ => rfl

/-- Inclusions of grades compose. -/
theorem sub_comp {k m n : ℕ∞} (h₁ : n ≤ m) (h₂ : m ≤ k) (P : PFunctor.{u, v}) :
    Lens.comp (sub h₁ P) (sub h₂ P) = sub (h₁.trans h₂) P :=
  lens_mk_congr fun _ _ => rfl

/-- The inclusions of grades are natural. -/
theorem sub_natural {m n : ℕ∞} (h : n ≤ m) (l : Lens P Q) :
    Lens.comp (sub h Q) (map m l) = Lens.comp (map n l) (sub h P) :=
  lens_mk_congr fun _ _ => rfl

/-- The inclusions of grades commute with the inclusion of the exponential. -/
theorem sub_ofBang {m n : ℕ∞} (h : n ≤ m) (P : PFunctor.{u, v}) :
    Lens.comp (sub h P) (ofBang m P) = ofBang n P :=
  lens_mk_congr fun _ _ => rfl

/-- The inclusion of the exponential is natural. -/
theorem ofBang_natural (n : ℕ∞) (l : Lens P Q) :
    Lens.comp (ofBang n Q) (bangMap l) = Lens.comp (map n l) (ofBang n P) :=
  lens_mk_congr fun _ _ => rfl

/-! ### The graded comonad -/

/-- The counit is natural. -/
theorem counit_natural (l : Lens P Q) :
    Lens.comp (counit Q) (map 1 l) = Lens.comp l (counit P) :=
  lens_mk_congr fun _ _ => Subtype.ext (Multiset.map_singleton _ _)

/-- The comultiplication is natural. -/
theorem comult_natural (m n : ℕ∞) (l : Lens P Q) :
    Lens.comp (comult m n Q) (map (m * n) l) = Lens.comp (map m (map n l)) (comult m n P) :=
  lens_mk_congr fun _ M => Subtype.ext (by
    simp [map, comult, Function.comp_def, Multiset.map_bind, Multiset.bind_map])

/-- The graded counit is the counit of the exponential. -/
theorem counit_ofBang (P : PFunctor.{u, v}) :
    Lens.comp (counit P) (ofBang 1 P) = bangCounit P :=
  lens_mk_congr fun _ _ => rfl

/-- The graded comultiplication is the comultiplication of the exponential. -/
theorem comult_ofBang (m n : ℕ∞) (P : PFunctor.{u, v}) :
    Lens.comp (comult m n P) (ofBang (m * n) P) =
      Lens.comp (map m (ofBang n P)) (Lens.comp (ofBang m (bang P)) (bangComult P)) :=
  lens_mk_congr fun _ M => by
    simp [comult, ofBang, map, bangComult, Lens.comp, Function.comp_def, Multiset.bind]

/-- Left counit law: the counit after the comultiplication at grades `1` and `n` is the inclusion
of `1 * n` in `n`. -/
theorem counit_comult (n : ℕ∞) (P : PFunctor.{u, v}) :
    Lens.comp (counit (bangLE n P)) (comult 1 n P) = sub (one_mul n).ge P :=
  lens_mk_congr fun _ _ => Subtype.ext (Multiset.singleton_bind _ _)

/-- Right counit law: the graded exponential of the counit after the comultiplication at grades
`n` and `1` is the inclusion of `n * 1` in `n`. -/
theorem map_counit_comult (n : ℕ∞) (P : PFunctor.{u, v}) :
    Lens.comp (map n (counit P)) (comult n 1 P) = sub (mul_one n).ge P :=
  lens_mk_congr fun _ s => Subtype.ext (by
    simp only [map, comult, counit, Function.comp_def, Multiset.bind_map]
    exact (Multiset.bind_singleton _ fun y => y).trans (Multiset.map_id' _))

/-- Coassociativity of the comultiplication, up to the inclusion of `m * n * k` in
`m * (n * k)`. -/
theorem comult_coassoc (m n k : ℕ∞) (P : PFunctor.{u, v}) :
    Lens.comp (comult m n (bangLE k P)) (comult (m * n) k P) =
      Lens.comp (map m (comult n k P))
        (Lens.comp (comult m (n * k) P) (sub (mul_assoc m n k).ge P)) :=
  lens_mk_congr fun _ M => Subtype.ext (by
    simp [map, comult, sub, Lens.comp, Function.comp_def, Multiset.bind_assoc,
      Multiset.bind_map])

/-! ### Weakening and contraction -/

/-- Contraction is natural. -/
theorem contr_natural (m n : ℕ∞) (l : Lens P Q) :
    Lens.comp (Lens.tensorMap (map m l) (map n l)) (contr m n P) =
      Lens.comp (contr m n Q) (map (m + n) l) :=
  lens_mk_congr fun _ _ => Subtype.ext (Multiset.map_add _ _ _).symm

/-- Weakening on the left after contraction is the left unitor, up to the inclusion of `0 + n`
in `n`. -/
theorem contr_weak_left (n : ℕ∞) (P : PFunctor.{u, v}) :
    Lens.comp (Lens.tensorMap (weak P) (Lens.id (bangLE n P))) (contr 0 n P) =
      Lens.comp Lens.Equiv.yTensor.invLens (sub (zero_add n).ge P) :=
  lens_mk_congr fun _ s => Subtype.ext (zero_add s.2.1)

/-- Weakening on the right after contraction is the right unitor, up to the inclusion of
`n + 0` in `n`. -/
theorem contr_weak_right (n : ℕ∞) (P : PFunctor.{u, v}) :
    Lens.comp (Lens.tensorMap (Lens.id (bangLE n P)) (weak P)) (contr n 0 P) =
      Lens.comp Lens.Equiv.tensorY.invLens (sub (add_zero n).ge P) :=
  lens_mk_congr fun _ s => Subtype.ext (add_zero s.1.1)

/-- Contraction is cocommutative, up to the inclusion of `m + n` in `n + m`. -/
theorem contr_comm (m n : ℕ∞) (P : PFunctor.{u, v}) :
    Lens.comp (Lens.Equiv.tensorComm (bangLE m P) (bangLE n P)).toLens (contr m n P) =
      Lens.comp (contr n m P) (sub (add_comm n m).le P) :=
  lens_mk_congr fun _ _ => Subtype.ext (add_comm _ _)

/-- Contraction is coassociative, up to the inclusion of `k + (m + n)` in `k + m + n`. -/
theorem contr_assoc (k m n : ℕ∞) (P : PFunctor.{u, v}) :
    Lens.comp (Lens.tensorMap (Lens.id (bangLE k P)) (contr m n P)) (contr k (m + n) P) =
      Lens.comp Lens.Equiv.tensorAssoc.toLens
        (Lens.comp (Lens.tensorMap (contr k m P) (Lens.id (bangLE n P)))
          (Lens.comp (contr (k + m) n P) (sub (add_assoc k m n).le P))) :=
  lens_mk_congr fun _ _ => Subtype.ext (add_assoc _ _ _).symm

/-- Graded contraction is the contraction of the exponential. -/
theorem contr_ofBang (m n : ℕ∞) (P : PFunctor.{u, v}) :
    Lens.comp (contr m n P) (ofBang (m + n) P) =
      Lens.comp (Lens.tensorMap (ofBang m P) (ofBang n P)) (bangContr P) :=
  lens_mk_congr fun _ _ => rfl

end bangLE

/-! ## Grades of Diller–Nahm morphisms -/

namespace DNLens

variable {P : PFunctor.{u₁, v₁}} {Q : PFunctor.{u₂, v₂}} {R : PFunctor.{u₃, v₃}}

/-- A Diller–Nahm morphism has grade `n` when each position of the target at the image of `a`
demands at most `n a` positions of the source. -/
def UsesLE (n : P.A → ℕ∞) (g : DNLens P Q) : Prop :=
  ∀ a y, ((g.toFunB a y).card : ℕ∞) ≤ n a

/-- A grade can be raised. -/
theorem UsesLE.mono {n n' : P.A → ℕ∞} {g : DNLens P Q} (hg : g.UsesLE n) (h : ∀ a, n a ≤ n' a) :
    g.UsesLE n' :=
  fun a y => (hg a y).trans (h a)

/-- The identity has grade `1`. -/
theorem usesLE_id (P : PFunctor.{u, v}) : (DNLens.id P).UsesLE fun _ => 1 :=
  fun _ _ => (congrArg Nat.cast (Multiset.card_singleton _)).le.trans (by simp)

/-- An ordinary lens has grade `1`. -/
theorem usesLE_ofLens (l : Lens P Q) : (ofLens l).UsesLE fun _ => 1 :=
  fun _ _ => by simp [ofLens]

/-- **Grades multiply along composition.** -/
theorem UsesLE.comp {g : DNLens Q R} {f : DNLens P Q} {m : Q.A → ℕ∞} {n : P.A → ℕ∞}
    (hg : g.UsesLE m) (hf : f.UsesLE n) :
    (DNLens.comp g f).UsesLE fun a => m (f.toFunA a) * n a :=
  fun a z => (card_bind_le fun x _ => hf a x).trans (mul_le_mul' (hg _ z) le_rfl)

/-- A morphism has constant grade `n` exactly when it is a lens out of the graded exponential
`bangLE n` followed by the inclusion of the exponential. -/
theorem usesLE_const_iff (n : ℕ∞) (g : DNLens P Q) :
    g.UsesLE (fun _ => n) ↔
      ∃ l : Lens (bangLE n P) Q, Lens.comp l (bangLE.ofBang n P) = g.toBangLens := by
  constructor
  · intro h
    exact ⟨⟨g.toFunA, fun a y => ⟨g.toFunB a y, h a y⟩⟩, rfl⟩
  · rintro ⟨l, hl⟩ a y
    have hg : g = ofBangLens (Lens.comp l (bangLE.ofBang n P)) := by
      rw [hl]
      rfl
    subst hg
    exact (l.toFunB a y).2

/-! ## Count matrices -/

/-- The count matrix at a shape: the multiplicity of the source position `x` in the demand of the
target position `y`. -/
def countMat [∀ a, DecidableEq (P.B a)] (g : DNLens P Q) (a : P.A) :
    Matrix (Q.B (g.toFunA a)) (P.B a) ℕ :=
  Matrix.of fun y x => (g.toFunB a y).count x

/-- **Composition is the product of count matrices.** -/
theorem countMat_comp [∀ b, Fintype (Q.B b)] [∀ a, DecidableEq (P.B a)]
    [∀ b, DecidableEq (Q.B b)] (g : DNLens Q R) (f : DNLens P Q) (a : P.A) :
    (DNLens.comp g f).countMat a = g.countMat (f.toFunA a) * f.countMat a := by
  ext z x
  simp only [countMat, DNLens.comp]
  exact count_bind_eq_sum _ _ _

/-- The count matrix of the identity is the identity matrix. -/
theorem countMat_id [∀ a, DecidableEq (P.B a)] (a : P.A) :
    (DNLens.id P).countMat a = (1 : Matrix (P.B a) (P.B a) ℕ) := by
  refine Matrix.ext fun (y : P.B a) x => ?_
  change Multiset.count x ({y} : Multiset (P.B a)) = _
  simp [Matrix.one_apply, Multiset.count_singleton, eq_comm]

/-- **A price is the linear map of the count matrix.** -/
theorem price_eq_mulVec [∀ a, Fintype (P.B a)] [∀ a, DecidableEq (P.B a)] (g : DNLens P Q)
    (p : ∀ a, P.B a → ℕ) (a : P.A) :
    g.price p a = (g.countMat a).mulVec (p a) := by
  funext y
  simp [price, countMat, Matrix.mulVec, dotProduct, multiset_sum_map_eq_sum_count]

/-- The number of positions demanded is the row sum of the count matrix. -/
theorem card_eq_sum_countMat [∀ a, Fintype (P.B a)] [∀ a, DecidableEq (P.B a)] (g : DNLens P Q)
    (a : P.A) (y : Q.B (g.toFunA a)) :
    (g.toFunB a y).card = ∑ x, g.countMat a y x := by
  simp [countMat]

end DNLens

/-! ## Use counts as upper triangular matrices -/

/-- The count matrix `[[n, c], [0, 1]]` of a costed function with `n` uses and cost `c`, rows and
columns ordered data token (`false`), clock tick (`true`). -/
def clockMat (n c : ℕ) : Matrix Bool Bool ℕ :=
  Matrix.of fun y x => bif y then (bif x then 1 else 0) else (bif x then c else n)

/-- **The composition law of use counts is the product of the affine matrices**: uses multiply,
and the cost is `c₂ + n₂ * c₁`. -/
theorem clockMat_mul (n₂ c₂ n₁ c₁ : ℕ) :
    clockMat n₂ c₂ * clockMat n₁ c₁ = clockMat (n₂ * n₁) (c₂ + n₂ * c₁) := by
  ext y x
  cases y <;> cases x <;> simp [clockMat, Matrix.mul_apply]

/-- The matrix of one use at no cost is the identity. -/
theorem clockMat_one : clockMat 1 0 = 1 := by
  ext y x
  cases y <;> cases x <;> simp [clockMat]

/-- The count matrix of the backward map with `n` uses and `c` clock ticks. -/
theorem countMat_clockBack (n c : ℕ) :
    Matrix.of (fun y x => (clockBack n c y).count x) = clockMat n c := by
  ext y x
  cases y <;> cases x <;> simp [clockBack, clockMat, Multiset.count_nsmul]

namespace Clocked

variable {X : Type u} {Y : Type v} {Z : Type w}

/-- The count matrix of a costed function with use counts is `[[uses, cost], [0, 1]]`. -/
theorem countMat_toDN (h : Clocked X Y) (a : X) :
    (toDN h).countMat a = clockMat (h.uses a) (h.cost a) :=
  countMat_clockBack _ _

/-- The composition law of `Clocked.toDN_comp`, derived from the product of count matrices. -/
theorem toDN_comp_of_countMat (g : Clocked Y Z) (f : Clocked X Y) :
    toDN (comp g f) = DNLens.comp (toDN g) (toDN f) :=
  DNLens.ext (fun _ => rfl) fun a b => Multiset.ext.2 fun x => by
    have h := congrFun (congrFun (DNLens.countMat_comp (toDN g) (toDN f) a) b) x
    rw [countMat_toDN, countMat_toDN, clockMat_mul] at h
    have h' := congrFun (congrFun (countMat_toDN (comp g f) a) b) x
    exact h'.trans h.symm

/-- A costed function with use counts has grade `max (uses + cost) 1`. -/
theorem usesLE_toDN (h : Clocked X Y) :
    (toDN h).UsesLE fun a => ((h.uses a + h.cost a : ℕ) : ℕ∞) ⊔ 1 := by
  intro a b
  cases b <;> simp [toDN, clockBack]

end Clocked

/-- The composition law `clockBack_bind` of backward maps, derived from the product of count
matrices. -/
theorem clockBack_bind_of_countMat (n₂ c₂ n₁ c₁ : ℕ) (b : Bool) :
    (clockBack n₂ c₂ b).bind (clockBack n₁ c₁) = clockBack (n₂ * n₁) (c₂ + n₂ * c₁) b :=
  (congrArg (fun g : DNLens (clockPos PUnit.{1}) (clockPos PUnit.{1}) => g.toFunB PUnit.unit b)
    (Clocked.toDN_comp_of_countMat (X := PUnit.{1}) ⟨id, fun _ => n₂, fun _ => c₂⟩
      ⟨id, fun _ => n₁, fun _ => c₁⟩)).symm

/-! ## Vector costs as unipotent matrices -/

section VecCosted

variable {ι : Type v₁} [DecidableEq ι]

/-- The count matrix `[[1, c], [0, 1]]` of a costed function with cost vector `c`, rows and columns
indexed by `none`, a data token, and `some i`, a tick of resource `i`. -/
def vecMat (c : ι →₀ ℕ) : Matrix (Option ι) (Option ι) ℕ :=
  Matrix.of fun y x => match y, x with
    | none, none => 1
    | none, some i => c i
    | some _, none => 0
    | some i, some j => if i = j then 1 else 0

/-- **The product of the matrices of two cost vectors is the matrix of their sum.** -/
theorem vecMat_mul [Fintype ι] (c₂ c₁ : ι →₀ ℕ) : vecMat c₂ * vecMat c₁ = vecMat (c₁ + c₂) := by
  ext y x
  cases y <;> cases x <;> simp [vecMat, Matrix.mul_apply, Fintype.sum_option]

/-- The matrix of the zero cost vector is the identity. -/
theorem vecMat_zero : vecMat (0 : ι →₀ ℕ) = 1 := by
  ext y x
  cases y <;> cases x <;> simp [vecMat, Matrix.one_apply]

namespace VecCosted

variable {X : Type u} {Y : Type v} {Z : Type w}

/-- The count matrix of the backward map of a cost vector. -/
theorem countMat_tokBack (c : ι →₀ ℕ) :
    Matrix.of (fun y x => (tokBack c y).count x) = vecMat c := by
  ext y x
  cases y <;> cases x <;> simp [tokBack, vecMat, Multiset.count_singleton, eq_comm,
    Multiset.count_map_eq_count' _ _ (Option.some_injective _)]

/-- The count matrix of a costed function with a cost vector is `[[1, cost], [0, 1]]`. -/
theorem countMat_toDN (h : VecCosted ι X Y) (a : X) : (toDN h).countMat a = vecMat (h.cost a) :=
  countMat_tokBack _

/-- The composition law of `VecCosted.toDN_comp` at finitely many resources, derived from the
product of count matrices. -/
theorem toDN_comp_of_countMat {ι : Type v₁} [Finite ι] (g : VecCosted ι Y Z)
    (f : VecCosted ι X Y) : toDN (comp g f) = DNLens.comp (toDN g) (toDN f) := by
  classical
  have := Fintype.ofFinite ι
  refine DNLens.ext (fun _ => rfl) fun a b => Multiset.ext.2 fun x => ?_
  have h := congrFun (congrFun (DNLens.countMat_comp (toDN g) (toDN f) a) b) x
  rw [countMat_toDN, countMat_toDN, vecMat_mul] at h
  have h' := congrFun (congrFun (countMat_toDN (comp g f) a) b) x
  exact h'.trans h.symm

end VecCosted

end VecCosted

/-! ## Use bounds of interpreted trees as vector–matrix products -/

section UseBound

open PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB}} {ι ι' : Type*} {α : Type uB}

/-- The sum of the rows of a matrix weighted by a vector is the vector–matrix product. -/
theorem vecMul_eq_sum_smul [Fintype ι] (u : ι → ℕ∞) (d : Matrix ι ι' ℕ∞) :
    Matrix.vecMul u d = ∑ i, u i • d i := by
  funext j
  simp [Matrix.vecMul, dotProduct, Finset.sum_apply]

/-- **The composition rule of use bounds as a vector–matrix product.** A tree with use bound `u`
interpreted by a handler whose call of an operation `a` has use bound `c a ⬝ d` has use bound
`u ⬝ d`, where row `i` of `d` is the use vector of one call of resource `i`. This is
`useBound_liftM` with the sum written as a product. -/
theorem useBound_liftM_vecMul [Fintype ι] {c : P.A → ι → ℕ∞} {allowsP : (a : P.A) → P.B a → Prop}
    {c' : Q.A → ι' → ℕ∞} {allows : (a : Q.A) → Q.B a → Prop} {x : FreeM P α} {u : ι → ℕ∞}
    {h : (a : P.A) → FreeM Q (P.B a)} {d : Matrix ι ι' ℕ∞} (hx : UseBound c allowsP x u)
    (hh : ∀ a, UseBound c' allows (h a) (Matrix.vecMul (c a) d))
    (hdem : ∀ a, wpFold (OpSpec.demonicUnder allows) (h a) (allowsP a)) :
    UseBound c' allows (x.liftM h) (Matrix.vecMul u d) := by
  rw [vecMul_eq_sum_smul]
  exact useBound_liftM hx (fun a => vecMul_eq_sum_smul (c a) d ▸ hh a) hdem

end UseBound

/-! ## The comonad laws of the weighted exponential -/

section Weighted

variable {S : Type w} [CommSemiring S]
variable {P : PFunctor.{u₁, v₁}} {Q : PFunctor.{u₂, v₂}} {R : PFunctor.{u₃, v₃}}

/-- The weighted exponential preserves identities. -/
theorem bangWMap_id : bangWMap (S := S) (Lens.id P) = Lens.id (bangW S P) :=
  lens_mk_congr fun _ _ => Finsupp.mapDomain_id

/-- The weighted exponential preserves composition. -/
theorem bangWMap_comp (m : Lens Q R) (l : Lens P Q) :
    bangWMap (S := S) (Lens.comp m l) = Lens.comp (bangWMap m) (bangWMap l) :=
  lens_mk_congr fun _ _ => by
    simp only [bangWMap, Lens.comp, Function.comp_apply]
    exact Finsupp.mapDomain_comp

/-- The counit of the weighted exponential is natural. -/
theorem bangWCounit_natural (l : Lens P Q) :
    Lens.comp (bangWCounit S Q) (bangWMap l) = Lens.comp l (bangWCounit S P) :=
  lens_mk_congr fun _ _ => Finsupp.mapDomain_single

/-- The comultiplication of the weighted exponential is natural. -/
theorem bangWComult_natural (l : Lens P Q) :
    Lens.comp (bangWComult S Q) (bangWMap l) =
      Lens.comp (bangWMap (bangWMap l)) (bangWComult S P) :=
  lens_mk_congr fun a (ww : (Q.B (l.toFunA a) →₀ S) →₀ S) => by
    change Finsupp.mapDomain (l.toFunB a) (Finsupp.linearCombination S id ww) =
      Finsupp.linearCombination S id (Finsupp.mapDomain (Finsupp.mapDomain (l.toFunB a)) ww)
    rw [Finsupp.linearCombination_mapDomain]
    exact Finsupp.apply_linearCombination_id S (Finsupp.lmapDomain S S (l.toFunB a)) ww

/-- Left counit law of the weighted exponential. -/
theorem bangWCounit_comult (P : PFunctor.{u, v}) :
    Lens.comp (bangWCounit S (bangW S P)) (bangWComult S P) = Lens.id (bangW S P) :=
  lens_mk_congr fun _ w => by
    change Finsupp.linearCombination S id (Finsupp.single w (1 : S)) = w
    simp [Finsupp.linearCombination_single]

/-- Right counit law of the weighted exponential. -/
theorem bangWMap_counit_comult (P : PFunctor.{u, v}) :
    Lens.comp (bangWMap (bangWCounit S P)) (bangWComult S P) = Lens.id (bangW S P) :=
  lens_mk_congr fun _ w => by
    change Finsupp.linearCombination S id (Finsupp.mapDomain (fun y => Finsupp.single y (1 : S)) w)
      = w
    rw [Finsupp.linearCombination_mapDomain]
    induction w using Finsupp.induction_linear <;> simp_all [Finsupp.linearCombination_single]

/-- Coassociativity of the comultiplication of the weighted exponential. -/
theorem bangWComult_coassoc (P : PFunctor.{u, v}) :
    Lens.comp (bangWComult S (bangW S P)) (bangWComult S P) =
      Lens.comp (bangWMap (bangWComult S P)) (bangWComult S P) :=
  lens_mk_congr fun _ www => by
    change Finsupp.linearCombination S id (Finsupp.linearCombination S id www) =
      Finsupp.linearCombination S id (Finsupp.mapDomain (Finsupp.linearCombination S id) www)
    rw [Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_linearCombination]
    rfl

end Weighted

/-- The weighted exponential as an endofunctor of the category of lenses, at weights in the
universe of positions. -/
noncomputable def bangWFunctor (S : Type v) [CommSemiring S] : LensCat.{u, v} ⥤ LensCat.{u, v} where
  obj X := LensCat.of (bangW S X.toPFunctor)
  map f := bangWMap f
  map_id _ := bangWMap_id
  map_comp f g := bangWMap_comp g f

/-- The weighted exponential as a comonad on the category of lenses. -/
noncomputable def bangWComonad (S : Type v) [CommSemiring S] : Comonad LensCat.{u, v} where
  toFunctor := bangWFunctor S
  ε := { app X := bangWCounit S X.toPFunctor, naturality _ _ f := bangWCounit_natural f }
  δ := { app X := bangWComult S X.toPFunctor, naturality _ _ f := bangWComult_natural f }
  coassoc X := (bangWComult_coassoc X.toPFunctor).symm
  left_counit X := bangWCounit_comult X.toPFunctor
  right_counit X := bangWMap_counit_comult X.toPFunctor

end CatCrypt.Container
