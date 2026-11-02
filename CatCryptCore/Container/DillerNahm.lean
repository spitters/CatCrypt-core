/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Multiset.Bind
public import PolyFun.PFunctor.Lens.Basic

/-!
# The Diller–Nahm category of containers and costed functions

The Diller–Nahm category (Moss and von Glehn, *Dialectica models of type theory*, LICS 2018, §8)
has the objects of polynomial functors. A morphism `P → Q` is a forward map `f` on shapes and a
backward map sending a position of `Q` at `f a` to a finite multiset of positions of `P` at `a`.
The composite of backward maps is the bind of the multiset monad.

A first-order costed function is a function `fn : X → Y` with a cost `cost : X → ℕ`, the form
`(X → Y) × (X → ℕ)` of the costed function types of the time certificates. It embeds in two
ways: as a lens on the objects `⟨X, ℕ⟩`, whose backward map is a translation by the cost, and
as a Diller–Nahm morphism on the objects `⟨X, Bool⟩`, whose position `false` is a data token and
whose position `true` is a clock tick. In the second form a data token of the output demands
data tokens of the input and clock ticks; the number of data tokens is the use count of the
input, and the costs compose by `c₂ + n₂ * c₁`.

## Main definitions

* `DNLens`, `DNLens.id`, `DNLens.comp`, `DNLens.ofLens` — the category and the ordinary lenses
  in it;
* `DNLens.price` — the value of a demanded multiset under a price of the input positions;
* `Costed`, `Costed.toLens`, `Costed.toDN` — costed functions and the two embeddings;
* `Clocked`, `Clocked.toDN`, `Clocked.toAffineLens` — costed functions with use counts;
* `VecCosted`, `VecCosted.toDN` — costs in `ι →₀ ℕ`, one clock for each resource `i`;
* `DNLens.pair` — the pairing into the product, whose positions are the sum of the positions.

## Main results

* `DNLens.id_comp`, `DNLens.comp_id`, `DNLens.comp_assoc`, `DNLens.ofLens_comp`;
* `DNLens.price_comp` — a price of a composite is the price of the price;
* `Costed.toLens_id`, `Costed.toLens_comp`, `Costed.toLens_injective`,
  `Costed.mem_range_toLens_iff` — the image of the first embedding is the translations;
* `Costed.toDN_id`, `Costed.toDN_comp`, `Costed.toDN_injective`, `Costed.equivIsLinear` — a
  costed function is a linear Diller–Nahm morphism;
* `Clocked.toDN_comp`, `Clocked.equivIsClocked` — uses multiply, and the cost of a composite is
  `c₂ + n₂ * c₁`;
* `Clocked.toAffineLens_comp` — the same composition law on the lenses with positions `ℕ → ℕ`;
* `VecCosted.toDN_comp` — the additive composition law of query counts;
* `DNLens.pair_comp_fst`, `DNLens.pair_comp_snd`, `DNLens.eq_pair` — the universal property of
  the pairing;
* `Costed.count_true_pair_both`, `Costed.count_true_pair_inl`,
  `Costed.count_true_pair_both_comp` — the clock ticks of a demand on a pairing.

Search words: Dialectica, Diller–Nahm, finite multiset, container, lens, cost, costed function,
use count, clock, query count, polynomial functor.
-/

set_option autoImplicit false

@[expose] public section

universe u v w u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

namespace CatCrypt.Container

open PFunctor

/-! ## The category -/

/-- A morphism of the Diller–Nahm category of containers: a forward map on shapes, and a backward
map from a position of `Q` to a finite multiset of positions of `P`. -/
structure DNLens (P : PFunctor.{u₁, v₁}) (Q : PFunctor.{u₂, v₂}) where
  /-- The forward map on shapes. -/
  toFunA : P.A → Q.A
  /-- The backward map on positions: the positions of `P` demanded by a position of `Q`. -/
  toFunB : ∀ a, Q.B (toFunA a) → Multiset (P.B a)

namespace DNLens

variable {P : PFunctor.{u₁, v₁}} {Q : PFunctor.{u₂, v₂}} {R : PFunctor.{u₃, v₃}}
  {S : PFunctor.{u₄, v₄}}

/-- Morphisms with equal forward maps and backward maps equal over them are equal. -/
theorem ext {f g : DNLens P Q} (hA : ∀ a, f.toFunA a = g.toFunA a)
    (hB : ∀ a y, f.toFunB a y = g.toFunB a (hA a ▸ y)) : f = g := by
  obtain ⟨fA, fB⟩ := f
  obtain ⟨gA, gB⟩ := g
  obtain rfl : fA = gA := funext hA
  congr
  funext a y
  exact hB a y

/-- The identity morphism: a position demands itself once. -/
protected def id (P : PFunctor.{u₁, v₁}) : DNLens P P where
  toFunA a := a
  toFunB _ y := {y}

/-- The composite `g ∘ f`: the forward maps compose, and each position demanded by `g` is replaced
by the multiset that `f` demands for it. -/
def comp (g : DNLens Q R) (f : DNLens P Q) : DNLens P R where
  toFunA a := g.toFunA (f.toFunA a)
  toFunB a z := (g.toFunB (f.toFunA a) z).bind (f.toFunB a)

/-- The identity is a left unit. -/
@[simp] theorem id_comp (f : DNLens P Q) : comp (DNLens.id Q) f = f :=
  ext (fun _ => rfl) fun _ _ => Multiset.singleton_bind _ _

/-- The identity is a right unit. -/
@[simp] theorem comp_id (f : DNLens P Q) : comp f (DNLens.id P) = f :=
  ext (fun _ => rfl) fun _ _ =>
    (Multiset.bind_singleton _ (fun y => y)).trans (Multiset.map_id' _)

/-- Composition is associative. -/
theorem comp_assoc (h : DNLens R S) (g : DNLens Q R) (f : DNLens P Q) :
    comp (comp h g) f = comp h (comp g f) :=
  ext (fun _ => rfl) fun _ _ => by simp [comp, Multiset.bind_assoc]

/-- An ordinary lens as a Diller–Nahm morphism: each position demands one position. -/
def ofLens (l : Lens P Q) : DNLens P Q where
  toFunA := l.toFunA
  toFunB a y := {l.toFunB a y}

/-- The inclusion of lenses preserves the identity. -/
theorem ofLens_id : ofLens (Lens.id P) = DNLens.id P :=
  ext (fun _ => rfl) fun _ _ => rfl

/-- The inclusion of lenses preserves composition. -/
theorem ofLens_comp (m : Lens Q R) (l : Lens P Q) :
    ofLens (Lens.comp m l) = comp (ofLens m) (ofLens l) :=
  ext (fun _ => rfl) fun _ _ => by simp [ofLens, comp, Lens.comp]

/-- The value of the multiset that `g` demands for `y`, under a price of the positions of `P`. -/
def price (g : DNLens P Q) (p : ∀ a, P.B a → ℕ) (a : P.A) (y : Q.B (g.toFunA a)) : ℕ :=
  ((g.toFunB a y).map (p a)).sum

/-- A price of a composite is the price under `g` of the price under `f`. The cost of a demand is
additive in the prices of the demanded positions, at dependent positions. -/
theorem price_comp (g : DNLens Q R) (f : DNLens P Q) (p : ∀ a, P.B a → ℕ) (a : P.A)
    (z : R.B (g.toFunA (f.toFunA a))) :
    (comp g f).price p a z =
      ((g.toFunB (f.toFunA a) z).map (f.price p a)).sum := by
  simp only [price, comp, Multiset.map_bind, Multiset.sum_bind]
  rfl

end DNLens

/-! ## Objects with constant positions -/

/-- The object with shapes `X` and a position `t : ℕ` at each shape, the time still needed. -/
abbrev natPos (X : Type u) : PFunctor.{u, 0} := ⟨X, fun _ => ℕ⟩

/-- The object with shapes `X` and the positions `false`, a data token, and `true`, a clock tick
at each shape. -/
abbrev clockPos (X : Type u) : PFunctor.{u, 0} := ⟨X, fun _ => Bool⟩

/-- A multiset of tokens is its data tokens and its clock ticks. -/
theorem multiset_bool_decomp (m : Multiset Bool) :
    m = m.count false • {false} + m.count true • {true} := by
  ext b
  cases b <;> simp

/-- The bind of a multiple of a multiset. -/
theorem nsmul_bind {α : Type u} {β : Type v} (n : ℕ) (s : Multiset α) (k : α → Multiset β) :
    (n • s).bind k = n • s.bind k := by
  induction n with
  | zero => simp
  | succ n ih => simp [succ_nsmul, ih]

/-! ## Costed functions -/

/-- A first-order costed function: a function with the cost of its evaluation at each argument. -/
@[ext] structure Costed (X : Type u) (Y : Type v) where
  /-- The function. -/
  fn : X → Y
  /-- The cost of evaluating `fn` at an argument. -/
  cost : X → ℕ

namespace Costed

variable {X : Type u} {Y : Type v} {Z : Type w} {W : Type u₁}

/-- The identity costs nothing. -/
protected def id (X : Type u) : Costed X X where
  fn a := a
  cost _ := 0

/-- The composite costs the cost of `f` at the argument plus the cost of `g` at the result. -/
def comp (g : Costed Y Z) (f : Costed X Y) : Costed X Z where
  fn a := g.fn (f.fn a)
  cost a := f.cost a + g.cost (f.fn a)

/-- The identity is a left unit. -/
@[simp] theorem id_comp (f : Costed X Y) : comp (Costed.id Y) f = f := by
  ext <;> simp [comp, Costed.id]

/-- The identity is a right unit. -/
@[simp] theorem comp_id (f : Costed X Y) : comp f (Costed.id X) = f := by
  ext <;> simp [comp, Costed.id]

/-- Composition is associative. -/
theorem comp_assoc (h : Costed Z W) (g : Costed Y Z) (f : Costed X Y) :
    comp (comp h g) f = comp h (comp g f) := by
  ext <;> simp [comp, Nat.add_assoc]

/-! ### The embedding in lenses -/

/-- A costed function as a lens: the backward map adds the cost to the time still needed. -/
def toLens (h : Costed X Y) : Lens (natPos X) (natPos Y) where
  toFunA := h.fn
  toFunB a (t : ℕ) := h.cost a + t

/-- The lens of the identity is the identity lens. -/
theorem toLens_id : toLens (Costed.id X) = Lens.id (natPos X) := by
  refine congrArg (Lens.mk _) (funext fun a => funext fun t => ?_)
  exact Nat.zero_add t

/-- The lens of a composite is the composite lens. -/
theorem toLens_comp (g : Costed Y Z) (f : Costed X Y) :
    toLens (comp g f) = Lens.comp (toLens g) (toLens f) := by
  refine congrArg (Lens.mk _) (funext fun a => funext fun t => ?_)
  exact Nat.add_assoc (f.cost a) (g.cost (f.fn a)) t

/-- The embedding in lenses is injective. -/
theorem toLens_injective : Function.Injective (toLens : Costed X Y → _) := by
  intro f g hfg
  have hA : f.fn = g.fn := congrArg Lens.toFunA hfg
  obtain ⟨ffn, fc⟩ := f
  obtain ⟨gfn, gc⟩ := g
  obtain rfl : ffn = gfn := hA
  have hB := eq_of_heq (Lens.mk.inj hfg).2
  obtain rfl : fc = gc := funext fun a => congrFun (congrFun hB a) 0
  rfl

/-- A lens on the objects `⟨X, ℕ⟩` whose backward map at each shape is a translation. -/
def IsTranslation (l : Lens (natPos X) (natPos Y)) : Prop :=
  ∀ a, ∃ c : ℕ, ∀ t : ℕ, l.toFunB a t = c + t

/-- The image of the embedding in lenses is exactly the translations. -/
theorem mem_range_toLens_iff (l : Lens (natPos X) (natPos Y)) :
    l ∈ Set.range (toLens : Costed X Y → _) ↔ IsTranslation l := by
  constructor
  · rintro ⟨h, rfl⟩ a
    exact ⟨h.cost a, fun _ => rfl⟩
  · intro hl
    choose c hc using hl
    refine ⟨⟨l.toFunA, c⟩, ?_⟩
    obtain ⟨lA, lB⟩ := l
    refine congrArg (Lens.mk _) (funext fun a => funext fun t => ?_)
    exact (hc a t).symm

end Costed

/-! ## Costed functions with use counts -/

/-- The backward map with `n` data tokens and `c` clock ticks for a data token, and one clock tick
for a clock tick. -/
def clockBack (n c : ℕ) : Bool → Multiset Bool
  | false => n • {false} + c • {true}
  | true => {true}

/-- The composite of two backward maps: uses multiply, and the clock ticks are the ticks of the
consumer plus its uses times the ticks of the producer. -/
theorem clockBack_bind (n₂ c₂ n₁ c₁ : ℕ) (b : Bool) :
    (clockBack n₂ c₂ b).bind (clockBack n₁ c₁) = clockBack (n₂ * n₁) (c₂ + n₂ * c₁) b := by
  cases b
  · simp only [clockBack, Multiset.add_bind, nsmul_bind, Multiset.singleton_bind, nsmul_add,
      add_nsmul, mul_nsmul']
    rw [add_assoc, add_comm (n₂ • c₁ • _)]
  · simp [clockBack]

/-- A costed function with use counts: for each argument, the number `uses` of times the input is
demanded by one use of the output, and the clock ticks `cost` of that use. -/
@[ext] structure Clocked (X : Type u) (Y : Type v) where
  /-- The function. -/
  fn : X → Y
  /-- The number of uses of the input for one use of the output. -/
  uses : X → ℕ
  /-- The clock ticks of one use of the output. -/
  cost : X → ℕ

namespace Clocked

variable {X : Type u} {Y : Type v} {Z : Type w} {W : Type u₁}

/-- The identity uses its input once and costs nothing. -/
protected def id (X : Type u) : Clocked X X where
  fn a := a
  uses _ := 1
  cost _ := 0

/-- The composite: uses multiply, and the cost is the cost of `g` plus its uses times the cost of
`f`. Each use of the result of `f` runs `f` again. -/
def comp (g : Clocked Y Z) (f : Clocked X Y) : Clocked X Z where
  fn a := g.fn (f.fn a)
  uses a := g.uses (f.fn a) * f.uses a
  cost a := g.cost (f.fn a) + g.uses (f.fn a) * f.cost a

/-- The Diller–Nahm morphism of a costed function with use counts. -/
def toDN (h : Clocked X Y) : DNLens (clockPos X) (clockPos Y) where
  toFunA := h.fn
  toFunB a := clockBack (h.uses a) (h.cost a)

/-- The morphism of the identity is the identity. -/
theorem toDN_id : toDN (Clocked.id X) = DNLens.id (clockPos X) := by
  refine DNLens.ext (fun _ => rfl) fun a b => ?_
  change clockBack 1 0 b = {b}
  cases b <;> simp [clockBack, one_nsmul]

/-- The morphism of a composite is the composite: `n = n₂ * n₁` and `c = c₂ + n₂ * c₁`. -/
theorem toDN_comp (g : Clocked Y Z) (f : Clocked X Y) :
    toDN (comp g f) = DNLens.comp (toDN g) (toDN f) :=
  DNLens.ext (fun _ => rfl) fun _ b => (clockBack_bind _ _ _ _ b).symm

/-- The data tokens of a data token are the uses. -/
theorem count_false_toDN (h : Clocked X Y) (a : X) :
    Multiset.count false ((toDN h).toFunB a false) = h.uses a := by
  simp [toDN, clockBack]

/-- The clock ticks of a data token are the cost. -/
theorem count_true_toDN (h : Clocked X Y) (a : X) :
    Multiset.count true ((toDN h).toFunB a false) = h.cost a := by
  simp [toDN, clockBack]

/-- The price of a data token: `uses` times the price of data plus `cost` times the price of a
tick. -/
theorem price_toDN (h : Clocked X Y) (p : ∀ _ : X, Bool → ℕ) (a : X) :
    (toDN h).price p a false = h.uses a * p a false + h.cost a * p a true := by
  simp [DNLens.price, toDN, clockBack, Multiset.nsmul_singleton]

/-- The Diller–Nahm morphisms on the objects `⟨X, Bool⟩` that send a tick to one tick. -/
def IsClocked (g : DNLens (clockPos X) (clockPos Y)) : Prop :=
  ∀ a, g.toFunB a true = {true}

/-- Costed functions with use counts are exactly the morphisms that send a tick to one tick. -/
def equivIsClocked : Clocked X Y ≃ {g : DNLens (clockPos X) (clockPos Y) // IsClocked g} where
  toFun h := ⟨toDN h, fun _ => rfl⟩
  invFun g :=
    { fn := g.1.toFunA
      uses a := Multiset.count false (g.1.toFunB a false)
      cost a := Multiset.count true (g.1.toFunB a false) }
  left_inv h := by
    ext a
    · rfl
    · exact count_false_toDN h a
    · exact count_true_toDN h a
  right_inv g := by
    obtain ⟨g, hg⟩ := g
    refine Subtype.ext (DNLens.ext (fun _ => rfl) fun a b => ?_)
    cases b
    · exact (multiset_bool_decomp (g.toFunB a false)).symm
    · exact (hg a).symm

/-- The lens of a costed function with use counts, on the positions `ℕ → ℕ`: the backward map
precomposes the affine map `T ↦ cost a + uses a * T`, from the time of the input to the time of
the output. -/
def toAffineLens (h : Clocked X Y) :
    Lens (⟨X, fun _ => ℕ → ℕ⟩ : PFunctor) (⟨Y, fun _ => ℕ → ℕ⟩ : PFunctor) where
  toFunA := h.fn
  toFunB a (k : ℕ → ℕ) := fun T => k (h.cost a + h.uses a * T)

/-- The lens of the identity is the identity lens. -/
theorem toAffineLens_id :
    toAffineLens (Clocked.id X) = Lens.id (⟨X, fun _ => ℕ → ℕ⟩ : PFunctor) := by
  refine congrArg (Lens.mk _) (funext fun a => funext fun k => funext fun T => ?_)
  change k (0 + 1 * T) = k T
  simp

/-- The lens of a composite is the composite lens: the law `n₂ * n₁`, `c₂ + n₂ * c₁` of the
Diller–Nahm form holds for ordinary lenses with the positions `ℕ → ℕ`. -/
theorem toAffineLens_comp (g : Clocked Y Z) (f : Clocked X Y) :
    toAffineLens (comp g f) = Lens.comp (toAffineLens g) (toAffineLens f) := by
  refine congrArg (Lens.mk _) (funext fun a => funext fun k => funext fun T => ?_)
  change k (g.cost (f.fn a) + g.uses (f.fn a) * f.cost a + g.uses (f.fn a) * f.uses a * T) =
    k (g.cost (f.fn a) + g.uses (f.fn a) * (f.cost a + f.uses a * T))
  congr 1
  rw [Nat.mul_add, Nat.add_assoc, Nat.mul_assoc]

/-- The lens of the use counts determines the costed function. -/
theorem toAffineLens_injective : Function.Injective (toAffineLens : Clocked X Y → _) := by
  intro f g hfg
  have hA : f.fn = g.fn := congrArg Lens.toFunA hfg
  obtain ⟨ffn, fn, fc⟩ := f
  obtain ⟨gfn, gn, gc⟩ := g
  obtain rfl : ffn = gfn := hA
  have hB := eq_of_heq (Lens.mk.inj hfg).2
  have key : ∀ a T, fc a + fn a * T = gc a + gn a * T := fun a T =>
    congrFun (congrFun (congrFun hB a) id) T
  have hc : fc = gc := funext fun a => by simpa using key a 0
  have hn : fn = gn := funext fun a => by
    have := key a 1
    rw [hc] at this
    simpa using this
  subst hc hn
  rfl

end Clocked

/-! ## The embedding of costed functions in the Diller–Nahm category -/

namespace Costed

variable {X : Type u} {Y : Type v} {Z : Type w} {W : Type u₁}

/-- A costed function as a costed function that uses its input once. -/
def toClocked (h : Costed X Y) : Clocked X Y where
  fn := h.fn
  uses _ := 1
  cost := h.cost

/-- The composite of costed functions is the case `n = 1` of the composite with use counts. -/
theorem toClocked_comp (g : Costed Y Z) (f : Costed X Y) :
    toClocked (comp g f) = Clocked.comp (toClocked g) (toClocked f) := by
  ext a <;> simp [toClocked, comp, Clocked.comp, Nat.add_comm]

/-- The Diller–Nahm morphism of a costed function: a tick demands a tick, and a data token
demands a data token and `cost a` ticks. -/
def toDN (h : Costed X Y) : DNLens (clockPos X) (clockPos Y) :=
  (toClocked h).toDN

/-- The backward map of `toDN` at a data token. -/
theorem toDN_false (h : Costed X Y) (a : X) :
    (toDN h).toFunB a false = {false} + h.cost a • {true} := by
  change 1 • {false} + h.cost a • {true} = _
  rw [one_nsmul]

/-- The morphism of the identity is the identity. -/
theorem toDN_id : toDN (Costed.id X) = DNLens.id (clockPos X) :=
  Clocked.toDN_id

/-- The morphism of a composite is the composite. -/
theorem toDN_comp (g : Costed Y Z) (f : Costed X Y) :
    toDN (comp g f) = DNLens.comp (toDN g) (toDN f) := by
  rw [toDN, toClocked_comp, Clocked.toDN_comp]
  rfl

/-- The morphisms on the objects `⟨X, Bool⟩` that send a tick to one tick and a data token to one
data token and ticks. -/
def IsLinear (g : DNLens (clockPos X) (clockPos Y)) : Prop :=
  (∀ a, g.toFunB a true = {true}) ∧ ∀ a, ∃ c : ℕ, g.toFunB a false = {false} + c • {true}

/-- A morphism is linear exactly when it sends a tick to one tick and a data token demands one data
token. -/
theorem isLinear_iff_count (g : DNLens (clockPos X) (clockPos Y)) :
    IsLinear g ↔ Clocked.IsClocked g ∧ ∀ a, Multiset.count false (g.toFunB a false) = 1 := by
  refine and_congr_right fun _ => forall_congr' fun a => ?_
  constructor
  · rintro ⟨c, hc⟩
    rw [hc]
    simp
  · intro h
    refine ⟨Multiset.count true (g.toFunB a false), ?_⟩
    have := multiset_bool_decomp (g.toFunB a false)
    rw [h, one_nsmul] at this
    exact this

/-- The morphism of a costed function is linear. -/
theorem isLinear_toDN (h : Costed X Y) : IsLinear (toDN h) :=
  ⟨fun _ => rfl, fun a => ⟨h.cost a, toDN_false h a⟩⟩

/-- A costed function is a linear element of the Diller–Nahm morphisms. -/
def equivIsLinear : Costed X Y ≃ {g : DNLens (clockPos X) (clockPos Y) // IsLinear g} where
  toFun h := ⟨toDN h, isLinear_toDN h⟩
  invFun g :=
    { fn := g.1.toFunA
      cost a := Multiset.count true (g.1.toFunB a false) }
  left_inv h := by
    ext a
    · rfl
    · exact Clocked.count_true_toDN (toClocked h) a
  right_inv g := by
    obtain ⟨g, hg⟩ := g
    refine Subtype.ext (DNLens.ext (fun _ => rfl) fun a b => ?_)
    cases b
    · have hc := (isLinear_iff_count g).1 hg
      have := multiset_bool_decomp (g.toFunB a false)
      rw [hc.2 a, one_nsmul] at this
      exact (toDN_false _ a).trans this.symm
    · exact (hg.1 a).symm

/-- The embedding in the Diller–Nahm category is injective. -/
theorem toDN_injective : Function.Injective (toDN : Costed X Y → _) := fun _ _ hfg =>
  equivIsLinear.injective (Subtype.ext hfg)

end Costed

/-! ## Vector costs -/

/-- A costed function with a cost for each resource `i : ι`, such as the queries to oracle `i`. -/
@[ext] structure VecCosted (ι : Type v₁) (X : Type u) (Y : Type v) where
  /-- The function. -/
  fn : X → Y
  /-- The cost of evaluating `fn` in each resource. -/
  cost : X → ι →₀ ℕ

namespace VecCosted

variable {ι : Type v₁} {X : Type u} {Y : Type v} {Z : Type w}

/-- The object with shapes `X` whose positions are `none`, a data token, and `some i`, a tick of
resource `i`. -/
abbrev tokPos (ι : Type v₁) (X : Type u) : PFunctor.{u, v₁} := ⟨X, fun _ => Option ι⟩

/-- The identity costs nothing. -/
protected def id (ι : Type v₁) (X : Type u) : VecCosted ι X X where
  fn a := a
  cost _ := 0

/-- The cost of a composite is the sum of the costs, in each resource. -/
noncomputable def comp (g : VecCosted ι Y Z) (f : VecCosted ι X Y) : VecCosted ι X Z where
  fn a := g.fn (f.fn a)
  cost a := f.cost a + g.cost (f.fn a)

/-- The backward map of a cost `c`: a tick of a resource demands one tick of that resource, and a
data token demands one data token and `c i` ticks of each resource `i`. -/
def tokBack (c : ι →₀ ℕ) : Option ι → Multiset (Option ι)
  | none => {none} + (Finsupp.toMultiset c).map some
  | some i => {some i}

/-- The Diller–Nahm morphism of a costed function with a cost for each resource. -/
def toDN (h : VecCosted ι X Y) : DNLens (tokPos ι X) (tokPos ι Y) where
  toFunA := h.fn
  toFunB a := tokBack (h.cost a)

/-- The morphism of the identity is the identity. -/
theorem toDN_id : toDN (VecCosted.id ι X) = DNLens.id (tokPos ι X) := by
  refine DNLens.ext (fun _ => rfl) fun a b => ?_
  change tokBack 0 b = {b}
  cases b <;> simp [tokBack]

/-- The additive composition law: the morphism of a composite, whose cost is `c₁ a + c₂ (f a)` in
`ι →₀ ℕ`, is the composite. -/
theorem toDN_comp (g : VecCosted ι Y Z) (f : VecCosted ι X Y) :
    toDN (comp g f) = DNLens.comp (toDN g) (toDN f) := by
  refine DNLens.ext (fun _ => rfl) fun a b => ?_
  change tokBack (f.cost a + g.cost (f.fn a)) b =
    (tokBack (g.cost (f.fn a)) b).bind (tokBack (f.cost a))
  cases b with
  | none =>
    simp only [tokBack, Multiset.add_bind, Multiset.singleton_bind, map_add, Multiset.map_add,
      Multiset.bind_map]
    rw [Multiset.bind_singleton, add_assoc]
  | some i => simp [tokBack]

/-- The ticks of resource `i` demanded by a data token are the cost in resource `i`. -/
theorem count_some_toDN [DecidableEq ι] (h : VecCosted ι X Y) (a : X) (i : ι) :
    Multiset.count (some i) ((toDN h).toFunB a none) = h.cost a i := by
  change Multiset.count (some i) ({none} + (Finsupp.toMultiset (h.cost a)).map some) = _
  rw [Multiset.count_add, Multiset.count_map_eq_count' _ _ (Option.some_injective ι),
    Finsupp.count_toMultiset]
  simp

/-- The embedding in the Diller–Nahm category is injective. -/
theorem toDN_injective : Function.Injective (toDN : VecCosted ι X Y → _) := by
  classical
  intro f g hfg
  have hA : f.fn = g.fn := congrArg DNLens.toFunA hfg
  ext1
  · exact hA
  · funext a
    ext i
    rw [← count_some_toDN f, ← count_some_toDN g, hfg]

end VecCosted

/-! ## Pairing -/

namespace DNLens

variable {P : PFunctor.{u₁, v₁}} {Q : PFunctor.{u₂, v₁}} {R : PFunctor.{u₃, v₃}}

/-- The first projection from the product, whose positions are the sum of the positions. -/
def fst (P : PFunctor.{u₁, v₁}) (Q : PFunctor.{u₂, v₁}) : DNLens (P.prod Q) P where
  toFunA ab := ab.1
  toFunB _ y := {Sum.inl y}

/-- The second projection from the product. -/
def snd (P : PFunctor.{u₁, v₁}) (Q : PFunctor.{u₂, v₁}) : DNLens (P.prod Q) Q where
  toFunA ab := ab.2
  toFunB _ y := {Sum.inr y}

/-- The pairing: a token of the left component demands what `f` demands, a token of the right
component what `g` demands. -/
def pair (f : DNLens R P) (g : DNLens R Q) : DNLens R (P.prod Q) where
  toFunA r := (f.toFunA r, g.toFunA r)
  toFunB r := Sum.elim (f.toFunB r) (g.toFunB r)

/-- The pairing followed by the first projection is the first component. -/
theorem pair_comp_fst (f : DNLens R P) (g : DNLens R Q) :
    comp (fst P Q) (pair f g) = f :=
  ext (fun _ => rfl) fun _ _ => Multiset.singleton_bind _ _

/-- The pairing followed by the second projection is the second component. -/
theorem pair_comp_snd (f : DNLens R P) (g : DNLens R Q) :
    comp (snd P Q) (pair f g) = g :=
  ext (fun _ => rfl) fun _ _ => Multiset.singleton_bind _ _

/-- A morphism into the product is the pairing of its projections. -/
theorem eq_pair (h : DNLens R (P.prod Q)) :
    h = pair (comp (fst P Q) h) (comp (snd P Q) h) := by
  refine ext (fun _ => rfl) fun r y => ?_
  cases y <;> simp [comp, fst, snd, pair]

end DNLens

namespace Costed

variable {X : Type u} {Y : Type v} {Z : Type w} {W : Type u₁}

/-- The pairing of two costed functions in the Diller–Nahm category. -/
abbrev pairDN (f : Costed X Y) (g : Costed X Z) :
    DNLens (clockPos X) ((clockPos Y).prod (clockPos Z)) :=
  DNLens.pair (toDN f) (toDN g)

/-- The demand of one data token of each component of a pairing. -/
def bothTokens (y : Y) (z : Z) : Multiset (((clockPos Y).prod (clockPos Z)).B (y, z)) :=
  {Sum.inl false} + {Sum.inr false}

/-- Demanding a data token of the left component costs the cost of that component only. -/
theorem count_true_pair_inl (f : Costed X Y) (g : Costed X Z) (a : X) :
    Multiset.count true ((pairDN f g).toFunB a (Sum.inl false)) = f.cost a :=
  Clocked.count_true_toDN (toClocked f) a

/-- Demanding a data token of the right component costs the cost of that component only. -/
theorem count_true_pair_inr (f : Costed X Y) (g : Costed X Z) (a : X) :
    Multiset.count true ((pairDN f g).toFunB a (Sum.inr false)) = g.cost a :=
  Clocked.count_true_toDN (toClocked g) a

/-- Demanding one data token of each component costs the sum of the costs. -/
theorem count_true_pair_both (f : Costed X Y) (g : Costed X Z) (a : X) :
    Multiset.count true ((bothTokens (f.fn a) (g.fn a)).bind ((pairDN f g).toFunB a)) =
      f.cost a + g.cost a := by
  rw [bothTokens, Multiset.add_bind, Multiset.singleton_bind, Multiset.singleton_bind,
    Multiset.count_add, count_true_pair_inl, count_true_pair_inr]

/-- Demanding one data token of each component demands two data tokens of the input. -/
theorem count_false_pair_both (f : Costed X Y) (g : Costed X Z) (a : X) :
    Multiset.count false ((bothTokens (f.fn a) (g.fn a)).bind ((pairDN f g).toFunB a)) = 2 := by
  rw [bothTokens, Multiset.add_bind, Multiset.singleton_bind, Multiset.singleton_bind,
    Multiset.count_add]
  exact congrArg₂ (· + ·) (Clocked.count_false_toDN (toClocked f) a)
    (Clocked.count_false_toDN (toClocked g) a)

/-- The clock ticks of a data token of a composite are the sum of the costs. -/
theorem count_true_comp_toDN (f : Costed Y Z) (h : Costed X Y) (a : X) :
    Multiset.count true ((DNLens.comp (toDN f) (toDN h)).toFunB a false) =
      h.cost a + f.cost (h.fn a) := by
  rw [← toDN_comp]
  exact Clocked.count_true_toDN (toClocked (comp f h)) a

/-- A producer `h` before a pairing runs once for each demanded component: demanding one data
token of each component costs the cost of `h` twice. -/
theorem count_true_pair_both_comp (f : Costed X Y) (g : Costed X Z) (h : Costed W X) (a : W) :
    Multiset.count true
        ((bothTokens (f.fn (h.fn a)) (g.fn (h.fn a))).bind
          ((DNLens.comp (pairDN f g) (toDN h)).toFunB a)) =
      2 * h.cost a + f.cost (h.fn a) + g.cost (h.fn a) := by
  rw [bothTokens, Multiset.add_bind, Multiset.singleton_bind, Multiset.singleton_bind,
    Multiset.count_add]
  have hl := count_true_comp_toDN f h a
  have hr := count_true_comp_toDN g h a
  change Multiset.count true ((DNLens.comp (toDN f) (toDN h)).toFunB a false) +
    Multiset.count true ((DNLens.comp (toDN g) (toDN h)).toFunB a false) = _
  grind only

end Costed

end CatCrypt.Container
