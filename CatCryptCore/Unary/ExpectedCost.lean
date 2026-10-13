/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCryptCore.Unary.ExpectationWP
public meta import CatCryptCore.Unary.Lossless
public meta import CatCryptCore.Prob.Support
public meta import CatCryptCore.Crypto.MonadCostModel
public meta import CatCryptCore.Unary.QueryBound
public meta import Mathlib.Algebra.Ring.GeomSum
public meta import Mathlib.Analysis.SpecificLimits.Basic

public meta section

set_option autoImplicit false

/-!
# Expected-cost transformer for `SPComp` (ert-style, over the expectation algebra)

A weakest-preexpectation-style **expected cost** transformer for CatCrypt's
stateful probability monad: cost is an explicit `ℕ`-valued resource threaded through
the computation, as the tick cost of Tachis (§3.3), and the
*expected* accumulated cost is computed by the same `OrderedMonadAlgebra
SDistr ℝ≥0∞` expectation algebra that powers `wpE`
(`CatCryptCore/Unary/ExpectationWP.lean`).

The motivating client is the expected running time of knowledge extractors.
A proof of knowledge whose extractor is a deterministic function of two
transcripts, and the worst-case cost of `MonadCostModel`/`SPTree.queryCost`,
do not describe Goldreich's knowledge extractor (Def. 4.7.2), whose **expected** running
time is bounded by `q / (p − κ)`; Bellare and Goldreich obtain such extractors by
repeating an attempt until it succeeds (§6, Prop. 6.1, and App. D). This file
supplies the quantitative layer:

1. `CostComp α := SPComp (α × ℕ)` — the minimal cost-instrumented wrapper:
   pair every result with its accumulated credit; `CostComp.bind` adds
   credits; `CostComp.charge`/`CostComp.lift` are the charged primitives.
2. `ecost c h` — expected accumulated cost from initial heap `h`, defined
   through `wpE` at the cost projection. Laws: `ecost_pure = 0`,
   `ecost_charge = price`, and the **tower law** `ecost_bind`
   (exact for lossless continuations, `ecost_bind_le` unconditionally —
   the `≤` direction is what every upper bound uses; on sub-distributions
   the equality direction fails because a run whose continuation fails discards the
   cost accumulated before it; the composition rule of the ert calculus is exact,
   since ert counts the time up to a halt).
3. Worst-case ⟹ expected (`ecost_compileCharged_le_queryCost`,
   `ecost_of_spTreeQueryAdm`): an `SPTree` syntax tree compiled with
   unit charges has expected cost bounded by its worst-case `queryCost` —
   the conservativity seam to `MonadCostModel`/`spTreeQueryAdm`.
4. The **geometric-retry theorem** (`ecost_retryN_le`,
   `ecost_retryN_le_div`): a retry loop with per-round expected cost `≤ C`
   and per-round failure probability `≤ 1 - p` has expected cost `≤ C / p`
   (truncated form `C * ∑_{i<n} q^i` for `n` rounds). This is the bound used for
   the retry construction of Bellare and Goldreich.

## Main definitions

* `CostComp` — cost-instrumented `SPComp`; `CostComp.pure`, `CostComp.bind`,
  `CostComp.charge`, `CostComp.lift`, charged primitives, `CostComp.erase`
* `ecost c h` — expected accumulated cost (via the expectation algebra)
* `compileCharged` — `SPTree` compilation with unit charge per operation
* `retryN body n` — bounded retry loop; `failProb body h` — per-round
  failure probability

## Main results

* `ecost_bind_le` / `ecost_bind` — the tower (additivity) law
* `ecost_compileCharged_le_queryCost`, `ecost_of_spTreeQueryAdm` —
  worst-case cost bounds are conservative over expected cost
* `compileCharged_erase` — instrumentation does not change semantics
* `ecost_retryN_le`, `ecost_retryN_le_geometric`, `ecost_retryN_le_div` —
  the geometric-retry bounds

## References

* Philipp G. Haselwarter, Kwing Hei Li, Markus de Medeiros, Simon Oddershede
  Gregersen, Alejandro Aguirre, Joseph Tassarotti, Lars Birkedal, *Tachis:
  Higher-Order Separation Logic with Credits for Expected Costs*,
  OOPSLA 2024 — our `ℕ` component is their tick cost (§3.3), whose expectation
  their credits bound (Thm. 2, adequacy).
* Benjamin Lucien Kaminski, Joost-Pieter Katoen, Christoph Matheja, Federico
  Olmedo, *Weakest Precondition Reasoning for Expected Runtimes of
  Randomized Algorithms*, J. ACM 65(5), 2018 (conference version ESOP 2016)
  — the ert calculus; `ecost_bind` corresponds to its sequential-composition rule
  (Table 1) in the additive form of Thm. 8.1, and `ecost_retryN_le` to an
  upper-invariant bound for a loop (Thm. 4.2; cf. Ex. 4.3), here obtained on top
  of the ordered-monad-algebra expectation modality of `ExpectationWP.lean`.
* Oded Goldreich, *Foundations of Cryptography* Vol. 1, Def. 4.7.2 — the
  knowledge extractor runs in expected time at most `q / (p − κ)`, with `p` the
  acceptance probability.
* Mihir Bellare, Oded Goldreich, *On Defining Proofs of Knowledge*, CRYPTO 1992,
  §6, Prop. 6.1 and App. D — repeating an extraction attempt until it succeeds
  gives expected time `poly / Pr[success]`. In `ecost_retryN_le_div`, `p` is the
  per-attempt success probability, not the `p` of Goldreich's Def. 4.7.2.
-/

namespace CatCrypt.Unary

open CatCrypt.Core CatCrypt.Prob
open scoped ENNReal

/-! ## Linearity of `wpE`

The expectation algebra is not just monotone but **linear**: `wpE`
distributes over pointwise sums and scalar multiples of postexpectations,
and is bounded by constants (with equality exactly for lossless programs —
on a strict sub-distribution a constant postexpectation only collects the
surviving mass). These are the laws that make additive cost accounting
work. -/

variable {α β γ : Type}

/-- `wpE` is additive in the postexpectation. -/
theorem wpE_add (c : SPComp α) (p q : α → Heap → ℝ≥0∞) (h : Heap) :
    wpE c (fun a h' => p a h' + q a h') h = wpE c p h + wpE c q h := by
  simp only [wpE_eq_tsum, mul_add]
  exact ENNReal.tsum_add

/-- `wpE` commutes with scalar multiplication of the postexpectation. -/
theorem wpE_const_mul (c : SPComp α) (k : ℝ≥0∞) (p : α → Heap → ℝ≥0∞) (h : Heap) :
    wpE c (fun a h' => k * p a h') h = k * wpE c p h := by
  simp only [wpE_eq_tsum]
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun x => by ring

@[simp] theorem wpE_zero (c : SPComp α) (h : Heap) :
    wpE c (fun _ _ => (0 : ℝ≥0∞)) h = 0 := by
  simp [wpE_eq_tsum]

/-- Pointwise-equal postexpectations give equal `wpE`. -/
theorem wpE_congr (c : SPComp α) {p q : α → Heap → ℝ≥0∞}
    (hpq : ∀ a h', p a h' = q a h') (h : Heap) : wpE c p h = wpE c q h := by
  have : p = q := funext fun a => funext fun h' => hpq a h'
  rw [this]

/-- `wpE` of a constant postexpectation is at most the constant
    (the constant times the surviving mass). -/
theorem wpE_const_le (c : SPComp α) (k : ℝ≥0∞) (h : Heap) :
    wpE c (fun _ _ => k) h ≤ k := by
  rw [wpE_eq_tsum, ENNReal.tsum_mul_right, tsum_some_eq_mass]
  calc SDistr.mass (c h) * k ≤ 1 * k := mul_le_mul' (sdistr_mass_le_one _) le_rfl
    _ = k := one_mul k

/-- For lossless programs, `wpE` of a constant is exactly the constant. -/
theorem wpE_const_of_lossless {c : SPComp α} (hc : isLossless c) (k : ℝ≥0∞) (h : Heap) :
    wpE c (fun _ _ => k) h = k := by
  rw [wpE_eq_tsum, ENNReal.tsum_mul_right, tsum_some_eq_mass, hc h, one_mul]

/-! ## `CostComp`: the cost-instrumented computation

The repo's cost accounting (`MonadCostModel`, `SPTree.queryCost`) is
worst-case and syntactic; `SPComp` itself carries no cost. `CostComp` is the
minimal cost-instrumented wrapper: a `WriterT ℕ`-shaped pairing of each
result with its accumulated credit, with `bind` adding credits. -/

/-- Cost-instrumented stateful probabilistic computation: each outcome
    carries its accumulated cost (in abstract credit units). -/
abbrev CostComp (α : Type) : Type := SPComp (α × ℕ)

namespace CostComp

/-- Return a value at zero cost. -/
noncomputable def pure (a : α) : CostComp α := SPComp.pure (a, 0)

/-- Charge `n` credits. -/
noncomputable def charge (n : ℕ) : CostComp Unit := SPComp.pure ((), n)

/-- Sequential composition; credits add. -/
noncomputable def bind (c : CostComp α) (f : α → CostComp β) : CostComp β :=
  SPComp.bind c fun p => SPComp.bind (f p.1) fun q => SPComp.pure (q.1, p.2 + q.2)

/-- Lift an uninstrumented computation at a flat price. -/
noncomputable def lift (c : SPComp α) (price : ℕ) : CostComp α :=
  SPComp.bind c fun a => SPComp.pure (a, price)

/-- Charged uniform sampling (unit cost). -/
noncomputable def sampleC (β : Type) [Fintype β] [Nonempty β] : CostComp β :=
  lift (SPComp.sample β) 1

/-- Charged heap read (unit cost). -/
noncomputable def getC (l : Location) : CostComp l.ty := lift (SPComp.get l) 1

/-- Charged heap write (unit cost). -/
noncomputable def setC (l : Location) (v : l.ty) : CostComp Unit :=
  lift (SPComp.set l v) 1

/-- Failure (collects no cost: the demonic-total modality drops the
    failing branch, matching `wpE`'s treatment of `none`). -/
noncomputable def fail : CostComp α := SPComp.fail

/-- Erase the instrumentation: project away the cost component. -/
noncomputable def erase (c : CostComp α) : SPComp α :=
  SPComp.bind c fun p => SPComp.pure p.1

end CostComp

/-! ## The expected-cost transformer -/

/-- **Expected accumulated cost** of a cost-instrumented computation from
    initial heap `h`: the weakest preexpectation of the cost projection,
    i.e. the expectation-algebra average of the credit component. -/
noncomputable def ecost (c : CostComp α) (h : Heap) : ℝ≥0∞ :=
  wpE c (fun p _ => (p.2 : ℝ≥0∞)) h

@[simp] theorem ecost_pure (a : α) (h : Heap) : ecost (CostComp.pure a) h = 0 := by
  unfold ecost CostComp.pure
  rw [wpE_pure]
  simp

@[simp] theorem ecost_charge (n : ℕ) (h : Heap) :
    ecost (CostComp.charge n) h = n := by
  unfold ecost CostComp.charge
  rw [wpE_pure]

@[simp] theorem ecost_fail (h : Heap) : ecost (CostComp.fail : CostComp α) h = 0 :=
  wpE_fail _ h

/-- A flat-priced lift costs at most its price (exactly the price times the
    surviving mass). -/
theorem ecost_lift_le (c : SPComp α) (price : ℕ) (h : Heap) :
    ecost (CostComp.lift c price) h ≤ price := by
  unfold ecost CostComp.lift
  rw [wpE_bind]
  have heq : (fun (a : α) (h' : Heap) =>
      wpE (SPComp.pure (a, price)) (fun p (_ : Heap) => (p.2 : ℝ≥0∞)) h')
      = fun _ _ => (price : ℝ≥0∞) := by
    funext a h'
    rw [wpE_pure]
  rw [heq]
  exact wpE_const_le c _ h

/-- A flat-priced lift of a lossless computation costs exactly its price. -/
theorem ecost_lift_of_lossless {c : SPComp α} (hc : isLossless c) (price : ℕ) (h : Heap) :
    ecost (CostComp.lift c price) h = price := by
  unfold ecost CostComp.lift
  rw [wpE_bind]
  have heq : (fun (a : α) (h' : Heap) =>
      wpE (SPComp.pure (a, price)) (fun p (_ : Heap) => (p.2 : ℝ≥0∞)) h')
      = fun _ _ => (price : ℝ≥0∞) := by
    funext a h'
    rw [wpE_pure]
  rw [heq]
  exact wpE_const_of_lossless hc _ h

/-! ### The tower law (additivity under `bind`)

`ecost (bind c f) = ecost c + E_c[ecost ∘ f]` — exact when the continuation
is lossless, `≤` unconditionally (on a strict sub-distribution the
continuation's first-phase credit is weighted by the surviving mass). The
`≤` direction is the one every upper bound consumes. -/

/-- **Tower law, bound form.** Expected cost of a sequence is at most the
    first phase's expected cost plus the `c`-average of the continuation's
    expected cost. -/
theorem ecost_bind_le (c : CostComp α) (f : α → CostComp β) (h : Heap) :
    ecost (CostComp.bind c f) h
      ≤ ecost c h + wpE c (fun p h' => ecost (f p.1) h') h := by
  unfold ecost CostComp.bind
  rw [wpE_bind]
  calc wpE c (fun p h' =>
        wpE (SPComp.bind (f p.1) fun q => SPComp.pure (q.1, p.2 + q.2))
          (fun r (_ : Heap) => (r.2 : ℝ≥0∞)) h') h
      ≤ wpE c (fun p h' =>
          (p.2 : ℝ≥0∞) + wpE (f p.1) (fun r (_ : Heap) => (r.2 : ℝ≥0∞)) h') h := by
        refine wpE_mono c (fun p h' => ?_) h
        rw [wpE_bind]
        have heq : (fun (q : β × ℕ) (h'' : Heap) =>
            wpE (SPComp.pure (q.1, p.2 + q.2)) (fun r (_ : Heap) => (r.2 : ℝ≥0∞)) h'')
            = fun q _ => ((p.2 : ℝ≥0∞) + (q.2 : ℝ≥0∞)) := by
          funext q h''
          rw [wpE_pure]
          push_cast
          rfl
        rw [heq, wpE_add]
        exact add_le_add (wpE_const_le _ _ _) le_rfl
    _ = wpE c (fun p _ => (p.2 : ℝ≥0∞)) h
        + wpE c (fun p h' => wpE (f p.1) (fun r (_ : Heap) => (r.2 : ℝ≥0∞)) h') h :=
        wpE_add c _ _ h

/-- **Tower law, exact form** for lossless continuations: expected cost of a
    sequence is the first phase's expected cost plus the `c`-average of the
    continuation's expected cost. -/
theorem ecost_bind (c : CostComp α) (f : α → CostComp β)
    (hf : ∀ a, isLossless (f a)) (h : Heap) :
    ecost (CostComp.bind c f) h
      = ecost c h + wpE c (fun p h' => ecost (f p.1) h') h := by
  unfold ecost CostComp.bind
  rw [wpE_bind]
  calc wpE c (fun p h' =>
        wpE (SPComp.bind (f p.1) fun q => SPComp.pure (q.1, p.2 + q.2))
          (fun r (_ : Heap) => (r.2 : ℝ≥0∞)) h') h
      = wpE c (fun p h' =>
          (p.2 : ℝ≥0∞) + wpE (f p.1) (fun r (_ : Heap) => (r.2 : ℝ≥0∞)) h') h := by
        refine wpE_congr c (fun p h' => ?_) h
        rw [wpE_bind]
        have heq : (fun (q : β × ℕ) (h'' : Heap) =>
            wpE (SPComp.pure (q.1, p.2 + q.2)) (fun r (_ : Heap) => (r.2 : ℝ≥0∞)) h'')
            = fun q _ => ((p.2 : ℝ≥0∞) + (q.2 : ℝ≥0∞)) := by
          funext q h''
          rw [wpE_pure]
          push_cast
          rfl
        rw [heq, wpE_add, wpE_const_of_lossless (hf p.1)]
    _ = wpE c (fun p _ => (p.2 : ℝ≥0∞)) h
        + wpE c (fun p h' => wpE (f p.1) (fun r (_ : Heap) => (r.2 : ℝ≥0∞)) h') h :=
        wpE_add c _ _ h

/-- Uniform-bound corollary of the tower law: `C₁`-bounded phase one plus
    `C₂`-bounded continuation gives a `C₁ + C₂` bound for the sequence. -/
theorem ecost_bind_le_add {c : CostComp α} {f : α → CostComp β} {C₁ C₂ : ℝ≥0∞}
    (hc : ∀ h, ecost c h ≤ C₁) (hf : ∀ a h, ecost (f a) h ≤ C₂) (h : Heap) :
    ecost (CostComp.bind c f) h ≤ C₁ + C₂ := by
  refine le_trans (ecost_bind_le c f h) (add_le_add (hc h) ?_)
  exact le_trans (wpE_mono c (fun p h' => hf p.1 h') h) (wpE_const_le c C₂ h)

/-! ### Erasure: instrumentation does not change semantics -/

@[simp] theorem erase_pure (a : α) :
    (CostComp.pure a).erase = SPComp.pure a := by
  unfold CostComp.erase CostComp.pure
  rw [SPComp.pure_bind]

@[simp] theorem erase_fail :
    (CostComp.fail : CostComp α).erase = SPComp.fail := by
  unfold CostComp.erase CostComp.fail
  rw [SPComp.fail_bind]

/-- Erasure is a monad morphism on `bind`. -/
theorem erase_bind (c : CostComp α) (f : α → CostComp β) :
    (CostComp.bind c f).erase = SPComp.bind c fun p => (f p.1).erase := by
  unfold CostComp.erase CostComp.bind
  rw [SPComp.bind_assoc]
  congr 1
  funext p
  rw [SPComp.bind_assoc]
  congr 1
  funext q
  rw [SPComp.pure_bind]

@[simp] theorem erase_lift (c : SPComp α) (price : ℕ) :
    (CostComp.lift c price).erase = c := by
  unfold CostComp.erase CostComp.lift
  rw [SPComp.bind_assoc]
  have heq : (fun (a : α) => SPComp.bind (SPComp.pure (a, price))
      fun p : α × ℕ => SPComp.pure p.1) = SPComp.pure (α := α) := by
    funext a
    rw [SPComp.pure_bind]
  rw [heq, SPComp.bind_pure]

/-- Binding a flat-priced lift, then erasing, is binding the uninstrumented
    computation against the erased continuation. -/
theorem erase_bind_lift (c : SPComp α) (price : ℕ) (f : α → CostComp β) :
    (CostComp.bind (CostComp.lift c price) f).erase
      = SPComp.bind c fun a => (f a).erase := by
  rw [erase_bind]
  unfold CostComp.lift
  rw [SPComp.bind_assoc]
  congr 1
  funext a
  rw [SPComp.pure_bind]

/-! ## Worst-case ⟹ expected: the `MonadCostModel` seam

`SPTree.queryCost` (the structural worst-case operation count behind
`UCMonad.spTreeQueryAdm`, the concrete query-bounded admissibility class of
`MonadCostModel.lean`) is **conservative** over expected cost: compiling a
syntax tree with a unit charge per operation yields expected cost at most
`queryCost`, while erasing the charges recovers `SPTree.compile` exactly. -/

/-- Compile a syntax tree with a unit charge per operation
    (the cost-instrumented sibling of `SPTree.compile`). -/
noncomputable def compileCharged : SPTree α → CostComp α
  | .ret a => CostComp.pure a
  | .sample β finβ neβ k =>
      letI := finβ; letI := neβ
      CostComp.bind (CostComp.sampleC β) fun b => compileCharged (k b)
  | .get l k => CostComp.bind (CostComp.getC l) fun v => compileCharged (k v)
  | .set l v t => CostComp.bind (CostComp.setC l v) fun _ => compileCharged t
  | .fail => CostComp.fail

/-- Erasing the charges recovers the standard compilation: the
    instrumentation is semantically invisible. -/
theorem compileCharged_erase (s : SPTree α) :
    (compileCharged s).erase = s.compile := by
  induction s with
  | ret a => simp [compileCharged, SPTree.compile]
  | sample β finβ neβ k ih =>
    show (CostComp.bind (CostComp.lift (SPComp.sample β) 1) fun b =>
      compileCharged (k b)).erase = _
    rw [erase_bind_lift]
    show _ = SPComp.bind (SPComp.sample β) fun b => (k b).compile
    congr 1
    funext b
    exact ih b
  | get l k ih =>
    show (CostComp.bind (CostComp.lift (SPComp.get l) 1) fun v =>
      compileCharged (k v)).erase = _
    rw [erase_bind_lift]
    show _ = SPComp.bind (SPComp.get l) fun v => (k v).compile
    congr 1
    funext v
    exact ih v
  | set l v t ih =>
    show (CostComp.bind (CostComp.lift (SPComp.set l v) 1) fun _ =>
      compileCharged t).erase = _
    rw [erase_bind_lift]
    show _ = SPComp.bind (SPComp.set l v) fun _ => t.compile
    congr 1
    funext u
    exact ih
  | fail => simp [compileCharged, SPTree.compile]

/-- **Conservativity**: the expected cost of the charged compilation is
    bounded by the worst-case operation count `SPTree.queryCost`. -/
theorem ecost_compileCharged_le_queryCost (s : SPTree α) (h : Heap) :
    ecost (compileCharged s) h ≤ (s.queryCost : ℝ≥0∞) := by
  induction s generalizing h with
  | ret a => simp [compileCharged]
  | sample β finβ neβ k ih =>
    letI := finβ; letI := neβ
    have hbound : ecost (CostComp.bind (CostComp.sampleC β) fun b =>
        compileCharged (k b)) h
        ≤ 1 + ((Finset.univ.sup fun b => (k b).queryCost : ℕ) : ℝ≥0∞) := by
      refine ecost_bind_le_add (fun h' => ?_) (fun b h' => ?_) h
      · show ecost (CostComp.lift (SPComp.sample β) 1) h' ≤ (1 : ℝ≥0∞)
        exact_mod_cast ecost_lift_le (SPComp.sample β) 1 h'
      · exact le_trans (ih b h')
          (Nat.cast_le.mpr
            (Finset.le_sup (f := fun b => (k b).queryCost) (Finset.mem_univ b)))
    refine le_trans hbound ?_
    show (1 : ℝ≥0∞) + _ ≤ ((1 + Finset.univ.sup fun b => (k b).queryCost : ℕ) : ℝ≥0∞)
    push_cast
    exact le_rfl
  | get l k ih =>
    have hbound : ecost (CostComp.bind (CostComp.getC l) fun v =>
        compileCharged (k v)) h
        ≤ 1 + ((Finset.univ.sup fun v => (k v).queryCost : ℕ) : ℝ≥0∞) := by
      refine ecost_bind_le_add (fun h' => ?_) (fun v h' => ?_) h
      · show ecost (CostComp.lift (SPComp.get l) 1) h' ≤ (1 : ℝ≥0∞)
        exact_mod_cast ecost_lift_le (SPComp.get l) 1 h'
      · exact le_trans (ih v h')
          (Nat.cast_le.mpr
            (Finset.le_sup (f := fun v => (k v).queryCost) (Finset.mem_univ v)))
    refine le_trans hbound ?_
    show (1 : ℝ≥0∞) + _ ≤ ((1 + Finset.univ.sup fun v => (k v).queryCost : ℕ) : ℝ≥0∞)
    push_cast
    exact le_rfl
  | set l v t ih =>
    have hbound : ecost (CostComp.bind (CostComp.setC l v) fun _ =>
        compileCharged t) h ≤ 1 + (t.queryCost : ℝ≥0∞) := by
      refine ecost_bind_le_add (fun h' => ?_) (fun _ h' => ih h') h
      show ecost (CostComp.lift (SPComp.set l v) 1) h' ≤ (1 : ℝ≥0∞)
      exact_mod_cast ecost_lift_le (SPComp.set l v) 1 h'
    refine le_trans hbound ?_
    show (1 : ℝ≥0∞) + _ ≤ ((1 + t.queryCost : ℕ) : ℝ≥0∞)
    push_cast
    exact le_rfl
  | fail => simp [compileCharged]

/-- **Worst-case admissibility ⟹ expected-cost instrumentation.** Any Kleisli
    arrow admissible for `UCMonad.spTreeQueryAdm` (the query-bounded
    `MonadCostModel`-style class) admits a cost instrumentation with the same
    semantics and expected cost uniformly bounded by the worst-case query
    bound. -/
theorem ecost_of_spTreeQueryAdm {f : α → SPComp β}
    (hadm : UCMonad.spTreeQueryAdm.adm f) :
    ∃ (g : α → CostComp β) (n : ℕ),
      (∀ a, (g a).erase = f a) ∧ ∀ a h, ecost (g a) h ≤ (n : ℝ≥0∞) := by
  obtain ⟨s, hs, n, hn⟩ := hadm
  refine ⟨fun a => compileCharged (s a), n, fun a => ?_, fun a h => ?_⟩
  · rw [compileCharged_erase, hs a]
  · exact le_trans (ecost_compileCharged_le_queryCost (s a) h)
      (Nat.cast_le.mpr (hn a))

/-! ## The geometric-retry theorem

The engine of rewinding-extractor analyses: a loop that retries a body until
it returns `some _`, with per-round expected cost `≤ C` and per-round failure
probability `≤ q`, has expected cost `≤ C * (1 + q + ⋯ + qⁿ⁻¹) ≤ C / (1-q)`. -/

/-- Bounded retry loop: run `body` up to `n` times, stopping at the first
    `some` result. -/
noncomputable def retryN (body : CostComp (Option β)) : ℕ → CostComp (Option β)
  | 0 => CostComp.pure none
  | n + 1 => CostComp.bind body fun r =>
      match r with
      | some b => CostComp.pure (some b)
      | none => retryN body n

/-- Probability that one round of the body fails (returns `none`). -/
noncomputable def failProb (body : CostComp (Option β)) (h : Heap) : ℝ≥0∞ :=
  wpE body (fun r _ => r.1.elim 1 fun _ => 0) h

/-- **Geometric-retry bound, truncated form.** If each round costs at most
    `C` in expectation and fails with probability at most `q`, then `n`
    rounds of retry cost at most `C * ∑_{i<n} qⁱ` in expectation. -/
theorem ecost_retryN_le (body : CostComp (Option β)) {C q : ℝ≥0∞}
    (hC : ∀ h, ecost body h ≤ C) (hq : ∀ h, failProb body h ≤ q) :
    ∀ (n : ℕ) (h : Heap),
      ecost (retryN body n) h ≤ C * ∑ i ∈ Finset.range n, q ^ i := by
  intro n
  induction n with
  | zero => intro h; simp [retryN]
  | succ n ih =>
    intro h
    refine le_trans (ecost_bind_le body _ h) ?_
    have hpoint : ∀ (p : Option β × ℕ) (h' : Heap),
        ecost (match p.1 with
          | some b => CostComp.pure (some b)
          | none => retryN body n) h'
          ≤ (C * ∑ i ∈ Finset.range n, q ^ i) * (p.1.elim 1 fun _ => 0) := by
      rintro ⟨r, m⟩ h'
      cases r with
      | none => simpa using ih h'
      | some b => simp
    have hmul := wpE_const_mul body (C * ∑ i ∈ Finset.range n, q ^ i)
      (fun r (_ : Heap) => r.1.elim 1 fun _ => 0) h
    calc ecost body h + wpE body (fun p h' => ecost (match p.1 with
            | some b => CostComp.pure (some b)
            | none => retryN body n) h') h
        ≤ C + wpE body (fun p _ =>
            (C * ∑ i ∈ Finset.range n, q ^ i) * (p.1.elim 1 fun _ => 0)) h :=
          add_le_add (hC h) (wpE_mono body hpoint h)
      _ = C + (C * ∑ i ∈ Finset.range n, q ^ i) * failProb body h := by
          rw [hmul]; rfl
      _ ≤ C + (C * ∑ i ∈ Finset.range n, q ^ i) * q :=
          add_le_add le_rfl (mul_le_mul' le_rfl (hq h))
      _ = C * (q * ∑ i ∈ Finset.range n, q ^ i + 1) := by ring
      _ = C * ∑ i ∈ Finset.range (n + 1), q ^ i := by rw [geom_sum_succ]

/-- **Geometric-retry bound, closed form**: `C / (1 - q)` independent of the
    retry budget. -/
theorem ecost_retryN_le_geometric (body : CostComp (Option β)) {C q : ℝ≥0∞}
    (hC : ∀ h, ecost body h ≤ C) (hq : ∀ h, failProb body h ≤ q)
    (n : ℕ) (h : Heap) :
    ecost (retryN body n) h ≤ C * (1 - q)⁻¹ := by
  refine le_trans (ecost_retryN_le body hC hq n h) (mul_le_mul' le_rfl ?_)
  exact le_trans (ENNReal.sum_le_tsum _) (le_of_eq (ENNReal.tsum_geometric q))

/-- **The `C / p` form** (the bound rewinding extractors quote): per-round
    success probability at least `p` and per-round expected cost at most `C`
    give expected total cost at most `C / p`, uniformly in the retry budget. -/
theorem ecost_retryN_le_div (body : CostComp (Option β)) {C p : ℝ≥0∞}
    (hp : p ≤ 1) (hC : ∀ h, ecost body h ≤ C)
    (hfail : ∀ h, failProb body h ≤ 1 - p) (n : ℕ) (h : Heap) :
    ecost (retryN body n) h ≤ C / p := by
  refine le_trans (ecost_retryN_le_geometric body hC hfail n h) ?_
  rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top hp, div_eq_mul_inv]

/-! ## Support plumbing

To prove that a rewinding extractor only ever outputs valid witnesses we
trace nonzero-probability outcomes backwards through `bind`/`pure`, using
`SDistr.bind_support_witness` from `CatCryptCore/Prob/Support.lean`. -/

/-- Support of an `SPComp` bind factors through an intermediate outcome. -/
theorem spcomp_bind_support {c : SPComp α} {f : α → SPComp β}
    {h : Heap} {b : β} {h' : Heap}
    (hne : (SPComp.bind c f h) (some (b, h')) ≠ 0) :
    ∃ a h₁, (c h) (some (a, h₁)) ≠ 0 ∧ (f a h₁) (some (b, h')) ≠ 0 := by
  obtain ⟨⟨a, h₁⟩, hca, hfa⟩ := SDistr.bind_support_witness hne
  exact ⟨a, h₁, hca, hfa⟩

/-- Support of an `SPComp.pure` is the singleton result/heap pair. -/
theorem spcomp_pure_support {a : α} {h : Heap} {b : α} {h' : Heap}
    (hne : (SPComp.pure a h) (some (b, h')) ≠ 0) : b = a ∧ h' = h := by
  have hmem : (a, h) = (b, h') := (SDistr.mem_support_pure_iff (a, h) (b, h')).mp hne
  exact ⟨(Prod.ext_iff.mp hmem).1.symm, (Prod.ext_iff.mp hmem).2.symm⟩

/-- Any successful (`some`) outcome of a retry loop traces back to a
    successful outcome of a single round of the body. -/
theorem retryN_support_some (body : CostComp (Option β)) :
    ∀ (n : ℕ) (h₀ : Heap) (b : β) (m : ℕ) (h' : Heap),
      (retryN body n h₀) (some ((some b, m), h')) ≠ 0 →
      ∃ h₁ m₁ h₂, (body h₁) (some ((some b, m₁), h₂)) ≠ 0 := by
  intro n
  induction n with
  | zero =>
    intro h₀ b m h' hne
    exfalso
    have hps := spcomp_pure_support (a := ((none : Option β), 0)) (h := h₀) hne
    have hcontra : (some b : Option β) = none := (Prod.ext_iff.mp hps.1).1
    simp at hcontra
  | succ n ih =>
    intro h₀ b m h' hne
    simp only [retryN, CostComp.bind] at hne
    obtain ⟨p, h₁, hbody, hinner⟩ := spcomp_bind_support hne
    obtain ⟨q, h₂, hk, hpure⟩ := spcomp_bind_support hinner
    obtain ⟨q1, q2⟩ := q
    have hq1 : q1 = some b := by
      have heq : (some b : Option β) = q1 :=
        (Prod.ext_iff.mp (spcomp_pure_support hpure).1).1
      exact heq.symm
    subst hq1
    obtain ⟨r, m₀⟩ := p
    cases r with
    | some b₀ =>
      have hqe := spcomp_pure_support hk
      have hb : b₀ = b := by
        have heq : (some b : Option β) = some b₀ := (Prod.ext_iff.mp hqe.1).1
        exact (Option.some.inj heq).symm
      subst hb
      exact ⟨h₀, m₀, h₁, hbody⟩
    | none =>
      exact ih h₁ b q2 h₂ hk

end CatCrypt.Unary
