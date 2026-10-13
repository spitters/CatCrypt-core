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

The Hasuo-style ordered-monad-algebra ("PT situation") development for
CatCrypt's probability monad: an `OrderedMonadAlgebra SDistr ℝ≥0∞` instance
whose algebra map `μ` is the **expected value** of a sub-distribution
(`SDistr α = PMF (Option α)`; the `none` branch contributes `0` — the
demonic-total modality, in which a failing computation satisfies no
postcondition).

This is the quantitative counterpart of the Boolean/conjunctive predicate
transformers of `Std.Do`: expectation is monotone but not conjunctive, so it
lives in an ordered-monad-algebra interface (a weakening of an
Eilenberg–Moore algebra on the truth-value carrier, after Hasuo's generic
weakest-precondition framework for order-enriched monads) rather than in
`PredTrans`.

The `OrderedMonadAlgebra` interface below is the standard categorical
structure for generic weakest preconditions: an Eilenberg–Moore-style
algebra `μ : m l → l` on an ordered carrier, used as a modality — Hasuo's
"monads enriched with order" framework (the unit law `μ_pure` plus
order-monotone binding suffice for monotone `wp`; the full EM
multiplication law corresponds to `wp_bind` holding as an equality, which
the `SDistr` instance proves). The same predicates-as-algebras reading
appears in Jacobs' state-and-effect triangles. The Lean interface shape
matches VCVio's `MAlgOrdered` (itself from Loom), so an
`MAlgOrdered SDistr ℝ≥0∞` instance is derived from this file's instance.

On top of the `SDistr` instance we define the heap-indexed weakest
preexpectation `wpE` for `SPComp α = Heap → SDistr (α × Heap)`, prove the
monad-morphism laws (`wpE_pure`, `wpE_bind`), and tie the construction to the
existing probability-of-event layer: `wpE` of an indicator postcondition is
exactly `CatCrypt.Unary.prEventComp` (and `CatCrypt.Crypto.prTrue` for
`Bool`-valued games).

## Main definitions

* `CatCrypt.OrderedMonadAlgebra` — minimal ordered-monad-algebra interface
  (`μ`, `μ_pure`, `μ_bind_mono`) with the induced `wp` and its laws
* `sdistrExpect` — expected value of `d : SDistr ℝ≥0∞` (`none` ↦ `0`)
* `instOrderedMonadAlgebraSDistr` — the `OrderedMonadAlgebra SDistr ℝ≥0∞`
  instance
* `wpE c post h` — heap-indexed weakest preexpectation for `SPComp`
* `TripleE pre c post` — heap-indexed quantitative triple
  `∀ h, pre h ≤ wpE c post h`

## Main results

* `wpE_pure` / `wpE_bind` / `wpE_mono` — the weakest-preexpectation laws
* `wpE_indicator_eq_prEventComp` — **adequacy**: `wpE` at an indicator
  postcondition is the event probability `prEventComp`
* `wpE_indicator_eq_prTrue` — adequacy specialized to `Bool` games / `prTrue`,
  the seam to the `Advantage` layer
* `wpE_sample` — `wpE` of a uniform sample is the average of the postcondition

## References

* Ichiro Hasuo, *Generic weakest precondition semantics from monads enriched
  with order*, Theoretical Computer Science 604, 2015 (conference version
  CMCS 2014) — the categorical source of this interface: ordered-monad
  algebras as wp modalities.
* Bart Jacobs, *A Recipe for State-and-Effect Triangles*, Logical Methods in
  Computer Science 13(2), 2017 (conference version CALCO 2015) — predicates
  as Eilenberg–Moore algebras.
* Kozen-style probabilistic PDL / McIver–Morgan weakest preexpectations —
  the concrete `ℝ≥0∞` instance.
* Engineering provenance of the Lean interface shape: VCVio's
  `ToMathlib/Control/Monad/Algebra.lean` (`MAlgOrdered`), after Loom
  (Gladshtein, Pîrlea, Zhao, Kurin, Sergey, *Foundational Multi-Modal
  Program Verifiers*, POPL 2026, doi:10.1145/3776719). Loom's own novelty
  claim is the *transformer*-level composition of such algebras; the
  single-monad ordered algebra used here is the classical notion
  (Hasuo's modality, with Kozen's expectation algebra as the concrete
  ancestor).
-/

namespace CatCrypt

open scoped ENNReal

/-! ## Ordered monad algebras

Minimal interface for quantitative wp/triple reasoning: an algebra map `μ`
from `m l` to the truth-value lattice `l`, respecting `pure` and monotone
under `bind`. Adapted from VCVio's `MAlgOrdered` (Loom-style), reproduced to
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

theorem wp_mono (x : m α) {post post' : α → l} (h : ∀ a, post a ≤ post' a) :
    wp x post ≤ wp x post' := by
  unfold wp
  exact μ_bind_mono
    (f := fun a => pure (post a))
    (g := fun a => pure (post' a))
    (fun a => by simpa [μ_pure] using h a)
    x

end OrderedMonadAlgebra

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
  classical
  unfold sdistrExpect
  rw [tsum_eq_single x (fun y hy => by simp [Ne.symm hy])]
  simp

@[simp] theorem sdistrExpect_fail : sdistrExpect (SDistr.fail) = 0 := by
  simp [sdistrExpect]

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
          simp

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
  rw [sdistrExpect_bind_eq_tsum]
  exact tsum_congr fun a => by rw [sdistrExpect_pure]

/-! ## Heap-indexed weakest preexpectation for `SPComp` -/

/-- Heap-indexed weakest preexpectation: the expected value of
    `post result finalHeap` when running `c` from initial heap `h`.
    Defined through the `OrderedMonadAlgebra SDistr ℝ≥0∞` instance. -/
noncomputable def wpE {α : Type} (c : SPComp α) (post : α → Heap → ℝ≥0∞) (h : Heap) : ℝ≥0∞ :=
  OrderedMonadAlgebra.wp (m := SDistr) (c h) (fun p => post p.1 p.2)

theorem wpE_eq_tsum {α : Type} (c : SPComp α) (post : α → Heap → ℝ≥0∞) (h : Heap) :
    wpE c post h = ∑' p : α × Heap, (c h) (some p) * post p.1 p.2 :=
  wp_sdistr_eq_tsum (c h) _

@[simp] theorem wpE_pure {α : Type} (a : α) (post : α → Heap → ℝ≥0∞) (h : Heap) :
    wpE (SPComp.pure a) post h = post a h := by
  classical
  rw [wpE_eq_tsum]
  show (∑' p : α × Heap, (SDistr.pure (a, h)) (some p) * post p.1 p.2) = post a h
  rw [tsum_eq_single (a, h) (fun p hp => by simp [Ne.symm hp])]
  simp

/-- `wpE` is a monad morphism on bind: the `wp_bind` law, heap-indexed. -/
theorem wpE_bind {α β : Type} (c : SPComp α) (f : α → SPComp β)
    (post : β → Heap → ℝ≥0∞) (h : Heap) :
    wpE (SPComp.bind c f) post h = wpE c (fun a h' => wpE (f a) post h') h := by
  unfold wpE
  show OrderedMonadAlgebra.wp (m := SDistr)
    ((c h) >>= fun p : α × Heap => f p.1 p.2) (fun p => post p.1 p.2) = _
  rw [OrderedMonadAlgebra.wp_bind]

@[simp] theorem wpE_fail {α : Type} (post : α → Heap → ℝ≥0∞) (h : Heap) :
    wpE (SPComp.fail) post h = 0 := by
  rw [wpE_eq_tsum]
  simp [SPComp.fail]

@[simp] theorem wpE_get (l : Location) (post : l.ty → Heap → ℝ≥0∞) (h : Heap) :
    wpE (SPComp.get l) post h = post (h.get l) h :=
  wpE_pure (a := h.get l) post h

@[simp] theorem wpE_set (l : Location) (v : l.ty) (post : Unit → Heap → ℝ≥0∞) (h : Heap) :
    wpE (SPComp.set l v) post h = post () (h.set l v) := by
  classical
  rw [wpE_eq_tsum]
  show (∑' p : Unit × Heap, (SDistr.pure ((), h.set l v)) (some p) * post p.1 p.2) = _
  rw [tsum_eq_single ((), h.set l v) (fun p hp => by simp [Ne.symm hp])]
  simp

theorem wpE_mono {α : Type} (c : SPComp α) {post post' : α → Heap → ℝ≥0∞}
    (hpost : ∀ a h', post a h' ≤ post' a h') (h : Heap) :
    wpE c post h ≤ wpE c post' h :=
  OrderedMonadAlgebra.wp_mono (m := SDistr) (c h) fun p => hpost p.1 p.2

/-! ## Quantitative triples for `SPComp` -/

/-- Heap-indexed quantitative Hoare triple: at every initial heap, the
    preexpectation lower-bounds the weakest preexpectation. -/
def TripleE {α : Type} (pre : Heap → ℝ≥0∞) (c : SPComp α) (post : α → Heap → ℝ≥0∞) : Prop :=
  ∀ h, pre h ≤ wpE c post h

theorem tripleE_pure {α : Type} (a : α) (post : α → Heap → ℝ≥0∞) :
    TripleE (fun h => post a h) (SPComp.pure a) post := by
  intro h; rw [wpE_pure]

theorem tripleE_conseq {α : Type} {pre pre' : Heap → ℝ≥0∞} {c : SPComp α}
    {post post' : α → Heap → ℝ≥0∞}
    (hpre : ∀ h, pre' h ≤ pre h) (hpost : ∀ a h', post a h' ≤ post' a h')
    (h : TripleE pre c post) : TripleE pre' c post' :=
  fun h₀ => le_trans (hpre h₀) (le_trans (h h₀) (wpE_mono c hpost h₀))

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
  rw [wpE_eq_tsum]
  unfold prEventComp prEvent
  refine tsum_congr fun p => ?_
  by_cases hE : E p.1 p.2 <;> simp [hE]

/-- Adequacy specialized to `Bool`-valued games: `wpE` of the `true`-indicator
    is `prTrue`, the quantity the `Advantage` layer is built from. -/
theorem wpE_indicator_eq_prTrue (G : SPComp Bool) (h : Heap) :
    wpE G (fun b _ => if b then 1 else 0) h = CatCrypt.Crypto.prTrue G h := by
  rw [wpE_eq_tsum]
  unfold CatCrypt.Crypto.prTrue
  rw [ENNReal.tsum_prod']
  rw [tsum_bool]
  simp

/-- Lower bounds on event probability are exactly indicator-postcondition
    preexpectation bounds (the `vcgen`-style lowering seam). -/
theorem le_prEventComp_iff_le_wpE {α : Type} (c : SPComp α) (E : α → Heap → Prop)
    [∀ a h', Decidable (E a h')] (h : Heap) (r : ℝ≥0∞) :
    r ≤ prEventComp c h E ↔ r ≤ wpE c (fun a h' => if E a h' then 1 else 0) h := by
  rw [wpE_indicator_eq_prEventComp]

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
        exact congrArg _ (funext hinner)
    _ = ∑' a : α, (SDistr.uniform α) (some a) * post a h := wp_sdistr_eq_tsum _ _
    _ = (Fintype.card α : ℝ≥0∞)⁻¹ * ∑' a : α, post a h := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun a => by rw [SDistr.uniform_apply_some]

/-- A uniform coin lands `true` with preexpectation `1/2`: the indicator
    adequacy plus `wpE_sample`, giving `prTrue`-level information for free. -/
example (h : Heap) :
    wpE (SPComp.sample Bool) (fun b _ => if b then 1 else 0) h = 2⁻¹ := by
  rw [wpE_sample]
  rw [tsum_bool]
  simp

end CatCrypt.Unary
