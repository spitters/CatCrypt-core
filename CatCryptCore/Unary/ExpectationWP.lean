/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCryptCore.Crypto.Advantage
public import CatCryptCore.Unary.Event


@[expose] public section
set_option autoImplicit false

/-!
# Quantitative weakest preexpectation for `SDistr` / `SPComp`

This file defines the interface `OrderedMonadAlgebra` (an algebra map `μ : m l → l` on an
ordered carrier with unit law `μ_pure` and monotone binding `μ_bind_mono`) with its induced
weakest precondition `wp`, and proves the laws `wp_pure`, `wp_bind` and `wp_mono` for every
instance. It gives an instance `OrderedMonadAlgebra SDistr ℝ≥0∞` whose map `μ` is the
expected value of a sub-distribution (`SDistr α = PMF (Option α)`; the `none` branch
contributes `0`). On `SPComp α = Heap → SDistr (α × Heap)` it defines the heap-indexed
weakest preexpectation `wpE`, proves its monad-morphism laws, and proves that `wpE` of an
indicator postcondition is the event probability `CatCrypt.Unary.prEventComp`, and
`CatCrypt.Crypto.prTrue` for `Bool`-valued games.

Expectation is monotone but not conjunctive, so it is stated through an ordered monad
algebra and not through the conjunctive predicate transformers `PredTrans` of `Std.Do`.

## Main definitions

* `CatCrypt.OrderedMonadAlgebra` — ordered-monad-algebra interface (`μ`, `μ_pure`,
  `μ_bind_mono`) with the induced `wp`
* `sdistrExpect` — expected value of `d : SDistr ℝ≥0∞` (`none` ↦ `0`)
* `instOrderedMonadAlgebraSDistr` — the `OrderedMonadAlgebra SDistr ℝ≥0∞` instance
* `wpE c post h` — heap-indexed weakest preexpectation for `SPComp`
* `TripleE pre c post` — heap-indexed quantitative triple `∀ h, pre h ≤ wpE c post h`

## Main results

* `wp_pure`, `wp_bind`, `wp_mono` — laws of `wp` for every instance
* `wpE_pure`, `wpE_bind`, `wpE_mono` — the weakest-preexpectation laws
* `wpE_indicator_eq_prEventComp` — `wpE` at an indicator postcondition is the event
  probability `prEventComp`
* `wpE_indicator_eq_prTrue` — the same for `Bool` games and `prTrue`
* `wpE_sample` — `wpE` of a uniform sample is the average of the postcondition

Relation to the literature: `CatCryptCore/Crypto/Complexity.md`.

## References

* Ichiro Hasuo, *Generic weakest precondition semantics from monads enriched
  with order*, Theoretical Computer Science 604, 2015 (conference version
  CMCS 2014) — Eilenberg–Moore algebras with a monotonicity condition as wp modalities
  (Def. 2.4), functoriality of the predicate transformer (Prop. 2.6, Thm. 2.14), the
  expectation modality `τ_total` (§2.3.3).
* Wataru Hino, Hiroki Kobayashi, Ichiro Hasuo, Bart Jacobs, *Healthiness from
  Duality*, LICS 2016 — Eilenberg–Moore algebras on an arbitrary poset of truth values
  with the pointwise monotonicity condition are the `Pos`-relative algebras, monad maps
  into the monotone continuation monad (Def. 4.2, Prop. 4.12).
* Kenji Maillard et al., *Dijkstra Monads for All*, ICFP 2019, §4.4 — effect observations
  into the monotone continuation monad correspond to monotone monad algebras.
* Bart Jacobs, *A Recipe for State-and-Effect Triangles*, Logical Methods in
  Computer Science 13(2), 2017 (conference version CALCO 2015) — predicate
  transformers beside state transformers (§2).
* Dexter Kozen, *Semantics of probabilistic programs*, J. Comput. Syst. Sci.
  22(3), 1981 (conference version FOCS 1979) — expectation as the probabilistic modality;
  unbounded `ℝ≥0∞` expectations as in Kaminski, Katoen, Matheja, Olmedo, J. ACM 65(5),
  2018, §8.
* Gladshtein, Pîrlea, Zhao, Kurin, Sergey, *Foundational Multi-Modal Program
  Verifiers*, POPL 2026, doi:10.1145/3776719 — ordered monad algebras (Def. 3.2,
  `MAlgOrdered`), the shape of the Lean interface.
-/

namespace CatCrypt

open scoped ENNReal

/-! ## Ordered monad algebras

Minimal interface for quantitative wp/triple reasoning: an algebra map `μ`
from `m l` to the truth-value lattice `l`, respecting `pure` and monotone
under `bind`. Adapted from `MAlgOrdered` of the PolyFun library
(`PolyFun/Control/Monad/Algebra.lean`, after Loom's `MonadAlgebras`), reproduced to
keep this foundational layer dependency-free. -/

universe u v

/-- Ordered monad algebra: a monotone Eilenberg–Moore-style algebra map on the
truth-value carrier `l`, inducing a weakest-precondition transformer `wp`. -/
class OrderedMonadAlgebra (m : Type u → Type v) (l : Type u)
    [Monad m] [CompleteLattice l] where
  /-- The algebra map (e.g. expectation for a probability monad). -/
  μ : m l → l
  /-- `μ` retracts `pure`. -/
  μ_pure : ∀ x : l, μ (pure x) = x
  /-- `μ ∘ bind` is monotone in the continuation. -/
  μ_bind_mono {α : Type u} :
    ∀ (f g : α → m l), (∀ a, μ (f a) ≤ μ (g a)) →
      ∀ x : m α, μ (x >>= f) ≤ μ (x >>= g)

namespace OrderedMonadAlgebra

variable {m : Type u → Type v} {l : Type u}
  [Monad m] [CompleteLattice l] [OrderedMonadAlgebra m l]
variable {α β : Type u}

/-- Weakest precondition induced by `μ`. -/
def wp (x : m α) (post : α → l) : l :=
  μ (x >>= fun a => pure (post a))

/-- `μ` of a bind only depends on the continuation through `μ`. -/
theorem μ_bind (x : m α) (f g : α → m l)
    (h : ∀ a, μ (f a) = μ (g a)) :
    μ (x >>= f) = μ (x >>= g) :=
  le_antisymm
    (μ_bind_mono f g (fun a => (h a).le) x)
    (μ_bind_mono g f (fun a => (h a).ge) x)

/-- The weakest pre-expectation of `pure x` is the postcondition at `x`. -/
@[simp]
theorem wp_pure [LawfulMonad m] (x : α) (post : α → l) :
    wp (pure x : m α) post = post x := by
  unfold wp
  simp [μ_pure]

/-- `wp` is a monad morphism on bind. -/
theorem wp_bind [LawfulMonad m] (x : m α) (f : α → m β) (post : β → l) :
    wp (x >>= f) post = wp x (fun a => wp (f a) post) := by
  unfold wp
  rw [bind_assoc]
  exact μ_bind x
    (fun a => f a >>= fun b => pure (post b))
    (fun a => pure (μ (f a >>= fun b => pure (post b))))
    (fun a => by
      simpa using
        (μ_pure (m := m) (l := l)
          (μ (f a >>= fun b => pure (post b)))).symm)

/-- `wp` is monotone in the postcondition. -/
theorem wp_mono (x : m α) {post post' : α → l} (h : ∀ a, post a ≤ post' a) :
    wp x post ≤ wp x post' := by
  unfold wp
  exact μ_bind_mono
    (f := fun a => pure (post a))
    (g := fun a => pure (post' a))
    (fun a => by simpa [μ_pure] using h a)
    x

/-- The Eilenberg–Moore multiplication law in Kleisli form: `μ (x >>= f)` depends on the
continuation `f` only through `μ ∘ f`. -/
theorem μ_bind_μ (x : m α) (f : α → m l) :
    μ (x >>= f) = μ (x >>= fun a => pure (μ (f a))) :=
  μ_bind x f (fun a => pure (μ (f a))) (fun a => (μ_pure (m := m) (μ (f a))).symm)

end OrderedMonadAlgebra

/-! ## Ordered monad algebras as Eilenberg–Moore algebras

An ordered monad algebra (Loom, Def. 3.2) is exactly an Eilenberg–Moore algebra
`τ : m l → l` that is order-congruent in the sense of Hasuo (TCS 2015, Def. 3.3):
`orderedMonadAlgebra_laws_iff`. Hasuo's Prop. 3.4 identifies order-congruence with the
monotonicity condition of a PT situation (Def. 2.4) on `Sets`, where the truth-value
carrier is `T Ω`, its order is the one given by the order-enrichment of `T`, and the order
on `Sets(X, T Ω)` is pointwise. Here the carrier `l` is any partial order, independent of
any order on `m`. -/

section EilenbergMoore

/-- Hasuo's order-congruence of `τ : m l → l` (TCS 2015, Def. 3.3, with `l` in the role of
`T Ω`): for every `α`, the map `t ↦ τ ∘ (t <$> ·)` from `α → l` to `m α → l` is monotone
for the pointwise orders. -/
def OrderCongruent {m : Type u → Type v} {l : Type u} [Functor m] [LE l]
    (τ : m l → l) : Prop :=
  ∀ {α : Type u} (t t' : α → l), (∀ a, t a ≤ t' a) →
    ∀ x : m α, τ (t <$> x) ≤ τ (t' <$> x)

variable {m : Type u → Type u} {l : Type u} [Monad m]

/-- The Eilenberg–Moore algebra laws for `τ : m l → l`: the unit law `τ ∘ pure = id` and
the multiplication law `τ ∘ join = τ ∘ map τ`, where `join X` is `X >>= id`. -/
def IsEMAlgebra (τ : m l → l) : Prop :=
  (∀ x : l, τ (pure x) = x) ∧ ∀ X : m (m l), τ (X >>= id) = τ (τ <$> X)

/-- For an Eilenberg–Moore algebra, `τ (x >>= f)` is `τ` of `x` mapped through `τ ∘ f`. -/
theorem IsEMAlgebra.bind_eq [LawfulMonad m] {τ : m l → l} (h : IsEMAlgebra τ)
    {α : Type u} (x : m α) (f : α → m l) :
    τ (x >>= f) = τ ((fun a => τ (f a)) <$> x) := by
  calc τ (x >>= f) = τ ((f <$> x) >>= id) := by rw [bind_map_left]; rfl
    _ = τ (τ <$> (f <$> x)) := h.2 _
    _ = τ ((fun a => τ (f a)) <$> x) := by rw [Functor.map_map]

/-- The laws of an ordered monad algebra (Loom, Def. 3.2: `μ_pure` and `μ_bind_mono`) hold
for `τ : m l → l` exactly when `τ` is an Eilenberg–Moore algebra that is order-congruent
in Hasuo's sense. -/
theorem orderedMonadAlgebra_laws_iff [LawfulMonad m] [PartialOrder l] (τ : m l → l) :
    ((∀ x : l, τ (pure x) = x) ∧
      ∀ {α : Type u} (f g : α → m l), (∀ a, τ (f a) ≤ τ (g a)) →
        ∀ x : m α, τ (x >>= f) ≤ τ (x >>= g)) ↔
    IsEMAlgebra τ ∧ OrderCongruent τ := by
  constructor
  · rintro ⟨hp, hb⟩
    refine ⟨⟨hp, fun X => ?_⟩, fun t t' h x => ?_⟩
    · rw [map_eq_pure_bind]
      exact le_antisymm (hb id _ (fun a => (hp (τ a)).ge) X)
        (hb _ id (fun a => (hp (τ a)).le) X)
    · rw [map_eq_pure_bind, map_eq_pure_bind]
      exact hb _ _ (fun a => by simpa [hp] using h a) x
  · rintro ⟨he, hc⟩
    refine ⟨he.1, fun f g hfg x => ?_⟩
    rw [he.bind_eq x f, he.bind_eq x g]
    exact hc _ _ hfg x

/-- An order-congruent Eilenberg–Moore algebra on a complete lattice is an ordered monad
algebra. -/
@[instance_reducible]
def OrderedMonadAlgebra.ofEilenbergMoore [LawfulMonad m] [CompleteLattice l]
    (τ : m l → l) (he : IsEMAlgebra τ) (hc : OrderCongruent τ) :
    OrderedMonadAlgebra m l where
  μ := τ
  μ_pure := he.1
  μ_bind_mono := ((orderedMonadAlgebra_laws_iff τ).2 ⟨he, hc⟩).2

/-- The algebra map of an ordered monad algebra is an Eilenberg–Moore algebra. -/
theorem OrderedMonadAlgebra.isEMAlgebra [LawfulMonad m] [CompleteLattice l]
    [OrderedMonadAlgebra m l] : IsEMAlgebra (OrderedMonadAlgebra.μ : m l → l) :=
  ((orderedMonadAlgebra_laws_iff _).1
    ⟨OrderedMonadAlgebra.μ_pure, OrderedMonadAlgebra.μ_bind_mono⟩).1

/-- The algebra map of an ordered monad algebra is order-congruent. -/
theorem OrderedMonadAlgebra.orderCongruent [LawfulMonad m] [CompleteLattice l]
    [OrderedMonadAlgebra m l] : OrderCongruent (OrderedMonadAlgebra.μ : m l → l) :=
  ((orderedMonadAlgebra_laws_iff _).1
    ⟨OrderedMonadAlgebra.μ_pure, OrderedMonadAlgebra.μ_bind_mono⟩).2

/-- The Eilenberg–Moore multiplication law for an ordered monad algebra:
`μ (join X) = μ (μ <$> X)`. -/
theorem OrderedMonadAlgebra.μ_join [LawfulMonad m] [CompleteLattice l]
    [OrderedMonadAlgebra m l] (X : m (m l)) :
    OrderedMonadAlgebra.μ (X >>= id) = OrderedMonadAlgebra.μ (OrderedMonadAlgebra.μ <$> X) :=
  OrderedMonadAlgebra.isEMAlgebra.2 X

end EilenbergMoore

end CatCrypt

namespace CatCrypt.Unary

open CatCrypt.Core CatCrypt.Prob
open scoped ENNReal

/-! ## Expectation algebra on `SDistr` -/

/-- Expected value of a sub-distribution over `ℝ≥0∞`.
    The failure branch (`none`) contributes `0`. -/
noncomputable def sdistrExpect (d : SDistr ℝ≥0∞) : ℝ≥0∞ :=
  ∑' x : ℝ≥0∞, d (some x) * x

@[simp] theorem sdistrExpect_pure (x : ℝ≥0∞) :
    sdistrExpect (SDistr.pure x) = x := by
  simp_all [sdistrExpect]

@[simp] theorem sdistrExpect_fail : sdistrExpect (SDistr.fail) = 0 := by
  simp_all [sdistrExpect]

/-- Expectation of a bind is the `d`-weighted sum of the continuation's
    expectations. -/
theorem sdistrExpect_bind_eq_tsum {α : Type} (d : SDistr α) (f : α → SDistr ℝ≥0∞) :
    sdistrExpect (SDistr.bind d f) = ∑' a : α, d (some a) * sdistrExpect (f a) := by
  unfold sdistrExpect SDistr.bind
  calc
    (∑' y, (PMF.bind d fun oa => match oa with
        | some a => f a | none => SDistr.fail) (some y) * y)
        = ∑' y, (∑' oa, d oa * (match oa with
            | some a => f a | none => SDistr.fail) (some y)) * y := by
          refine tsum_congr fun y => ?_
          rw [PMF.bind_apply]
    _ = ∑' y, ∑' oa, d oa * (match oa with
            | some a => f a | none => SDistr.fail) (some y) * y := by
          refine tsum_congr fun y => ?_
          rw [ENNReal.tsum_mul_right]
    _ = ∑' oa, ∑' y, d oa * (match oa with
            | some a => f a | none => SDistr.fail) (some y) * y := ENNReal.tsum_comm
    _ = ∑' oa, d oa * ∑' y, (match oa with
            | some a => f a | none => SDistr.fail) (some y) * y := by
          refine tsum_congr fun oa => ?_
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr fun y => (mul_assoc _ _ _)
    _ = ∑' a : α, d (some a) * ∑' y, (f a) (some y) * y := by
          refine SDistr.tsum_option_none_zero _ ?_
          simp_all

/-- `SDistr` is a quantitative (Hasuo-style) ordered monad algebra over `ℝ≥0∞`:
    the algebra map is expectation, with failure collapsing to `⊥ = 0`. -/
noncomputable instance instOrderedMonadAlgebraSDistr :
    OrderedMonadAlgebra SDistr ℝ≥0∞ where
  μ := sdistrExpect
  μ_pure x := sdistrExpect_pure x
  μ_bind_mono f g hfg x := by
    show sdistrExpect (SDistr.bind x f) ≤ sdistrExpect (SDistr.bind x g)
    rw [sdistrExpect_bind_eq_tsum, sdistrExpect_bind_eq_tsum]
    exact ENNReal.tsum_le_tsum fun a => mul_le_mul' le_rfl (hfg a)

/-- `OrderedMonadAlgebra.wp` on `SDistr` unfolded as a weighted sum. -/
theorem wp_sdistr_eq_tsum {α : Type} (d : SDistr α) (post : α → ℝ≥0∞) :
    OrderedMonadAlgebra.wp (m := SDistr) d post = ∑' a : α, d (some a) * post a := by
  show sdistrExpect (SDistr.bind d fun a => SDistr.pure (post a)) = _
  simp_all [sdistrExpect_bind_eq_tsum, sdistrExpect_pure]

/-! ## Heap-indexed weakest preexpectation for `SPComp` -/

/-- Heap-indexed weakest preexpectation: the expected value of
    `post result finalHeap` when running `c` from initial heap `h`.
    Defined through the `OrderedMonadAlgebra SDistr ℝ≥0∞` instance. -/
noncomputable def wpE {α : Type} (c : SPComp α) (post : α → Heap → ℝ≥0∞) (h : Heap) : ℝ≥0∞ :=
  OrderedMonadAlgebra.wp (m := SDistr) (c h) (fun p => post p.1 p.2)

/-- `wpE` as a sum over the outcomes of the computation, weighted by their probabilities. -/
theorem wpE_eq_tsum {α : Type} (c : SPComp α) (post : α → Heap → ℝ≥0∞) (h : Heap) :
    wpE c post h = ∑' p : α × Heap, (c h) (some p) * post p.1 p.2 :=
  wp_sdistr_eq_tsum (c h) _

@[simp] theorem wpE_pure {α : Type} (a : α) (post : α → Heap → ℝ≥0∞) (h : Heap) :
    wpE (SPComp.pure a) post h = post a h := by
  solve_by_elim [sdistrExpect_pure, sdistrExpect_fail, wpE_eq_tsum, wp_sdistr_eq_tsum,
      CatCrypt.OrderedMonadAlgebra.μ_bind, CatCrypt.OrderedMonadAlgebra.wp_bind, CatCrypt.OrderedMonadAlgebra.wp_pure,
      CatCrypt.IsEMAlgebra.bind_eq, sdistrExpect_bind_eq_tsum, CatCrypt.OrderedMonadAlgebra.μ_bind_μ,
      CatCrypt.OrderedMonadAlgebra.μ_join, CatCrypt.orderedMonadAlgebra_laws_iff]

/-- `wpE` is a monad morphism on bind: the `wp_bind` law, heap-indexed. -/
theorem wpE_bind {α β : Type} (c : SPComp α) (f : α → SPComp β)
    (post : β → Heap → ℝ≥0∞) (h : Heap) :
    wpE (SPComp.bind c f) post h = wpE c (fun a h' => wpE (f a) post h') h := by
  solve_by_elim [wpE_pure, sdistrExpect_pure, wpE_eq_tsum, sdistrExpect_fail, wp_sdistr_eq_tsum,
      CatCrypt.OrderedMonadAlgebra.μ_bind, sdistrExpect_bind_eq_tsum, CatCrypt.OrderedMonadAlgebra.wp_bind,
      CatCrypt.OrderedMonadAlgebra.wp_pure, CatCrypt.IsEMAlgebra.bind_eq, CatCrypt.OrderedMonadAlgebra.μ_bind_μ,
      CatCrypt.OrderedMonadAlgebra.μ_join, CatCrypt.orderedMonadAlgebra_laws_iff]

@[simp] theorem wpE_fail {α : Type} (post : α → Heap → ℝ≥0∞) (h : Heap) :
    wpE (SPComp.fail) post h = 0 := by
  simp_all [wpE_eq_tsum, SPComp.fail]

@[simp] theorem wpE_get (l : Location) (post : l.ty → Heap → ℝ≥0∞) (h : Heap) :
    wpE (SPComp.get l) post h = post (h.get l) h :=
  wpE_pure (a := h.get l) post h

@[simp] theorem wpE_set (l : Location) (v : l.ty) (post : Unit → Heap → ℝ≥0∞) (h : Heap) :
    wpE (SPComp.set l v) post h = post () (h.set l v) := by
  solve_by_elim [wpE_pure, wpE_bind, wpE_fail, wpE_get, sdistrExpect_pure, sdistrExpect_fail, wpE_eq_tsum,
      wp_sdistr_eq_tsum, sdistrExpect_bind_eq_tsum, CatCrypt.OrderedMonadAlgebra.μ_bind,
      CatCrypt.OrderedMonadAlgebra.wp_bind, CatCrypt.OrderedMonadAlgebra.wp_pure, CatCrypt.IsEMAlgebra.bind_eq,
      CatCrypt.OrderedMonadAlgebra.μ_bind_μ, CatCrypt.OrderedMonadAlgebra.μ_join]

/-- `wpE` is monotone in the post-expectation. -/
theorem wpE_mono {α : Type} (c : SPComp α) {post post' : α → Heap → ℝ≥0∞}
    (hpost : ∀ a h', post a h' ≤ post' a h') (h : Heap) :
    wpE c post h ≤ wpE c post' h :=
  OrderedMonadAlgebra.wp_mono (m := SDistr) (c h) fun p => hpost p.1 p.2

/-- `wpE` is additive in the postexpectation. -/
theorem wpE_add {α : Type} (c : SPComp α) (p q : α → Heap → ℝ≥0∞) (h : Heap) :
    wpE c (fun a h' => p a h' + q a h') h = wpE c p h + wpE c q h := by
  simp_all [wpE_eq_tsum, mul_add, ENNReal.tsum_add]

/-- `wpE` commutes with scalar multiplication of the postexpectation. -/
theorem wpE_const_mul {α : Type} (c : SPComp α) (k : ℝ≥0∞) (p : α → Heap → ℝ≥0∞) (h : Heap) :
    wpE c (fun a h' => k * p a h') h = k * wpE c p h := by
  grind [wpE_eq_tsum, ENNReal.tsum_mul_left, tsum_congr]

/-! ## Quantitative triples for `SPComp` -/

/-- Heap-indexed quantitative Hoare triple: at every initial heap, the
    preexpectation lower-bounds the weakest preexpectation. -/
def TripleE {α : Type} (pre : Heap → ℝ≥0∞) (c : SPComp α) (post : α → Heap → ℝ≥0∞) : Prop :=
  ∀ h, pre h ≤ wpE c post h

/-- Expectation triple for `pure`. -/
theorem tripleE_pure {α : Type} (a : α) (post : α → Heap → ℝ≥0∞) :
    TripleE (fun h => post a h) (SPComp.pure a) post := by
  intro h; rw [wpE_pure]

/-- Consequence rule: strengthen the pre-expectation bound and weaken the post-expectation. -/
theorem tripleE_conseq {α : Type} {pre pre' : Heap → ℝ≥0∞} {c : SPComp α}
    {post post' : α → Heap → ℝ≥0∞}
    (hpre : ∀ h, pre' h ≤ pre h) (hpost : ∀ a h', post a h' ≤ post' a h')
    (h : TripleE pre c post) : TripleE pre' c post' :=
  fun h₀ => le_trans (hpre h₀) (le_trans (h h₀) (wpE_mono c hpost h₀))

/-- Sequencing rule: compose two expectation triples through an intermediate expectation `cut`. -/
theorem tripleE_bind {α β : Type} {pre : Heap → ℝ≥0∞} {c : SPComp α}
    {cut : α → Heap → ℝ≥0∞} {f : α → SPComp β} {post : β → Heap → ℝ≥0∞}
    (hc : TripleE pre c cut) (hf : ∀ a, TripleE (cut a) (f a) post) :
    TripleE pre (SPComp.bind c f) post := by
  intro h
  rw [wpE_bind]
  exact le_trans (hc h) (wpE_mono c (fun a h' => hf a h') h)

/-! ## Adequacy: `wpE` of indicators is event probability

These lemmas tie the ordered-monad-algebra picture to CatCrypt's existing
probability-of-event machinery (`CatCrypt.Unary.prEventComp`,
`CatCrypt.Crypto.prTrue`), and hence to the `Advantage` layer. -/

/-- **Adequacy.** The weakest preexpectation of the indicator of an event `E`
    is exactly the probability that `E` holds for `c` started at heap `h`. -/
theorem wpE_indicator_eq_prEventComp {α : Type} (c : SPComp α) (E : α → Heap → Prop)
    [∀ a h', Decidable (E a h')] (h : Heap) :
    wpE c (fun a h' => if E a h' then 1 else 0) h = prEventComp c h E := by
  grind [wpE_eq_tsum, prEventComp, prEvent, tsum_congr]

/-- Adequacy specialized to `Bool`-valued games: `wpE` of the `true`-indicator
    is `prTrue`, the quantity the `Advantage` layer is built from. -/
theorem wpE_indicator_eq_prTrue (G : SPComp Bool) (h : Heap) :
    wpE G (fun b _ => if b then 1 else 0) h = CatCrypt.Crypto.prTrue G h := by
  simp_all [wpE_eq_tsum, ENNReal.tsum_prod', CatCrypt.Crypto.prTrue]

/-- Lower bounds on event probability are exactly indicator-postcondition
    preexpectation bounds (the `vcgen`-style lowering seam). -/
theorem le_prEventComp_iff_le_wpE {α : Type} (c : SPComp α) (E : α → Heap → Prop)
    [∀ a h', Decidable (E a h')] (h : Heap) (r : ℝ≥0∞) :
    r ≤ prEventComp c h E ↔ r ≤ wpE c (fun a h' => if E a h' then 1 else 0) h := by
  simp_all [wpE_indicator_eq_prEventComp]

/-- Event probability, as an exact quantitative triple. -/
theorem tripleE_prEventComp {α : Type} (c : SPComp α) (E : α → Heap → Prop)
    [∀ a h', Decidable (E a h')] :
    TripleE (fun h => prEventComp c h E) c (fun a h' => if E a h' then 1 else 0) :=
  fun h => le_of_eq (wpE_indicator_eq_prEventComp c E h).symm

/-! ## Examples -/

/-- `wpE` of a uniform sample is the average of the postcondition over the
    sampled type (heap unchanged). -/
theorem wpE_sample (α : Type) [Fintype α] [Nonempty α]
    (post : α → Heap → ℝ≥0∞) (h : Heap) :
    wpE (SPComp.sample α) post h =
      (Fintype.card α : ℝ≥0∞)⁻¹ * ∑' a : α, post a h := by
  unfold wpE SPComp.sample
  show OrderedMonadAlgebra.wp (m := SDistr)
    ((SDistr.uniform α) >>= fun a => SDistr.pure (a, h)) (fun p => post p.1 p.2) = _
  rw [OrderedMonadAlgebra.wp_bind]
  have hinner : ∀ a : α,
      OrderedMonadAlgebra.wp (m := SDistr) (SDistr.pure (a, h))
        (fun p => post p.1 p.2) = post a h := by
    intro a
    rw [wp_sdistr_eq_tsum]
    classical
    rw [tsum_eq_single (a, h) (fun p hp => by simp [Ne.symm hp])]
    simp
  calc OrderedMonadAlgebra.wp (m := SDistr) (SDistr.uniform α)
        (fun a => OrderedMonadAlgebra.wp (m := SDistr) (SDistr.pure (a, h))
          (fun p => post p.1 p.2))
      = OrderedMonadAlgebra.wp (m := SDistr) (SDistr.uniform α) (fun a => post a h) := by
        simp_all [congrArg]
    _ = ∑' a : α, (SDistr.uniform α) (some a) * post a h := wp_sdistr_eq_tsum _ _
    _ = (Fintype.card α : ℝ≥0∞)⁻¹ * ∑' a : α, post a h := by
        rw [← ENNReal.tsum_mul_left]
        simp_all [SDistr.uniform_apply_some]

/-- A uniform coin lands `true` with preexpectation `1/2`: the indicator
    adequacy plus `wpE_sample`, giving `prTrue`-level information for free. -/
example (h : Heap) :
    wpE (SPComp.sample Bool) (fun b _ => if b then 1 else 0) h = 2⁻¹ := by
  rw [wpE_sample]
  rw [tsum_bool]
  simp

end CatCrypt.Unary
