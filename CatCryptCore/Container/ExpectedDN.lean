/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.DillerNahm
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Basic.NNReal.Basic
public import CatCryptCore.ForMathlib.GeometricMean

/-!
# Expected demands: the Diller–Nahm category over finitely supported measures

The backward map of a morphism of the Diller–Nahm category (`DNLens`) sends a position of the
output to a finite multiset of positions of the input, its demand. A morphism with expected
demands (`EDNLens`) sends it to a finitely supported measure on the positions of the input, with
nonnegative real weights `P.B a →₀ ℝ≥0`: the expected number of times each position is demanded.
A finite multiset is such a measure with natural weights. Composition is the bind of the monad of
finitely supported measures, `Finsupp.linearCombination` of the demands of the producer weighted
by the demand of the consumer, and the price of a demand is its expectation (`EDNLens.price`), so
that the price of a composite is the price under the consumer of the price under the producer
(`EDNLens.price_comp`): the linearity of expectation.

A costed function with expected use counts (`EClocked`) has, at each argument, the expected
number of uses of its input and the expected clock ticks of one use of its output; its morphism
sends a data token to the measure `uses • δ_data + cost • δ_tick` (`EClocked.toEDN`). Composition
multiplies the expected uses and adds the consumer's ticks to its expected uses times the
producer's ticks (`EClocked.toEDN_comp`), and the expected time of one use, `cost + uses * T` at
the expected time `T` of a use of the input, is the price of a data token (`EClocked.time_eq_price`)
and composes as the time of `Clocked` does (`EClocked.time_comp`). This is the expected-time
certificate: the expected time of a composite is the expected time of the consumer at the expected
time of the producer, when each use of the input runs the producer afresh (Wald's identity for a
number of uses independent of the producer's runs).

The rewinding loop with geometric retries (`retryClocked`): a loop that repeats a trial, each trial
succeeding with probability `p > 0`, makes `N + 1` trials where `N` is geometric with parameter
`p`. Its expected number of trials is `1 / p` (`expected_trials_geometric`, the mean of
`ProbabilityTheory.geometricMeasure`), so the loop is the costed function with expected uses
`1 / p` of its trial, and its expected time at a trial of expected time `T` is `(c + T) / p` for a
cost `c` of the loop per trial (`retryClocked_time`).

## Main definitions

* `EDNLens`, `EDNLens.id`, `EDNLens.comp`, `EDNLens.price`
* `EClocked`, `EClocked.toEDN`, `EClocked.time`, `EClocked.timePrice`
* `retryClocked`

## Main results

* `EDNLens.id_comp`, `EDNLens.comp_id`, `EDNLens.comp_assoc`, `EDNLens.price_comp`
* `EClocked.toEDN_id`, `EClocked.toEDN_comp`, `EClocked.time_eq_price`, `EClocked.time_comp`
* `EClocked.time_mono`
* `expected_trials_geometric`, `retryClocked_time`, `retryClocked_comp_time`,
  `retryClocked_time_le`

## References

* S. Moss, T. von Glehn, *Dialectica models of type theory*, LICS 2018, §8;
* A. Wald, *On cumulative sums of random variables*, Ann. Math. Statist. 15 (1944).

Search words: expected time, expected cost, finitely supported measure, Diller–Nahm, Dialectica,
linearity of expectation, geometric distribution, rewinding, retry loop, Wald's identity.
-/

@[expose] public section

set_option autoImplicit false

open scoped NNReal

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

namespace CatCrypt.Container

open PFunctor

/-! ## The category -/

/-- A morphism with expected demands: a forward map on shapes, and a backward map from a position
of `Q` to a finitely supported measure on the positions of `P`, the expected number of times each
is demanded. -/
structure EDNLens (P : PFunctor.{u₁, v₁}) (Q : PFunctor.{u₂, v₂}) where
  /-- The forward map on shapes. -/
  toFunA : P.A → Q.A
  /-- The backward map: the expected demand of a position of `Q` on the positions of `P`. -/
  toFunB : ∀ a, Q.B (toFunA a) → (P.B a →₀ ℝ≥0)

namespace EDNLens

variable {P : PFunctor.{u₁, v₁}} {Q : PFunctor.{u₂, v₂}} {R : PFunctor.{u₃, v₃}}
  {S : PFunctor.{u₄, v₄}}

/-- Morphisms with equal forward maps and backward maps equal over them are equal. -/
theorem ext {f g : EDNLens P Q} (hA : ∀ a, f.toFunA a = g.toFunA a)
    (hB : ∀ a y, f.toFunB a y = g.toFunB a (hA a ▸ y)) : f = g := by
  obtain ⟨fA, fB⟩ := f
  obtain ⟨gA, gB⟩ := g
  obtain rfl : fA = gA := funext hA
  congr
  funext a y
  exact hB a y

/-- The identity: a position demands itself once. -/
protected noncomputable def id (P : PFunctor.{u₁, v₁}) : EDNLens P P where
  toFunA a := a
  toFunB _ y := Finsupp.single y 1

/-- The composite `g ∘ f`: each position demanded by `g` is replaced by the expected demand of `f`
on it, weighted: the bind of finitely supported measures. -/
noncomputable def comp (g : EDNLens Q R) (f : EDNLens P Q) : EDNLens P R where
  toFunA a := g.toFunA (f.toFunA a)
  toFunB a z := Finsupp.linearCombination ℝ≥0 (f.toFunB a) (g.toFunB (f.toFunA a) z)

/-- The identity is a left unit. -/
@[simp] theorem id_comp (f : EDNLens P Q) : comp (EDNLens.id Q) f = f :=
  ext (fun _ => rfl) fun _ _ => by
    exact (Finsupp.linearCombination_single ℝ≥0 (v := f.toFunB _) 1 _).trans (one_smul _ _)

/-- The identity is a right unit. -/
@[simp] theorem comp_id (f : EDNLens P Q) : comp f (EDNLens.id P) = f := by
  refine ext (fun _ => rfl) fun a y => ?_
  change Finsupp.linearCombination ℝ≥0 (fun x => Finsupp.single x (1 : ℝ≥0)) (f.toFunB a y) = _
  rw [Finsupp.linearCombination_apply]
  simp only [Finsupp.smul_single_one, Finsupp.sum_single]

/-- Composition is associative. -/
theorem comp_assoc (h : EDNLens R S) (g : EDNLens Q R) (f : EDNLens P Q) :
    comp (comp h g) f = comp h (comp g f) :=
  ext (fun _ => rfl) fun _ _ => by
    simp only [comp, Finsupp.linearCombination_linearCombination]

/-- The expected price of the demand of `y` under a price of the positions of `P`. -/
noncomputable def price (g : EDNLens P Q) (p : ∀ a, P.B a → ℝ≥0) (a : P.A)
    (y : Q.B (g.toFunA a)) : ℝ≥0 :=
  Finsupp.linearCombination ℝ≥0 (p a) (g.toFunB a y)

/-- **The price of a composite** is the price under `g` of the price under `f`: the linearity of
expectation. -/
theorem price_comp (g : EDNLens Q R) (f : EDNLens P Q) (p : ∀ a, P.B a → ℝ≥0) (a : P.A)
    (z : R.B (g.toFunA (f.toFunA a))) :
    (comp g f).price p a z =
      Finsupp.linearCombination ℝ≥0 (f.price p a) (g.toFunB (f.toFunA a) z) := by
  exact Finsupp.linearCombination_linearCombination (R := ℝ≥0) _ _ _

end EDNLens

/-! ## Costed functions with expected use counts -/

/-- A costed function with expected use counts: for each argument, the expected number of uses of
the input for one use of the output, and the expected clock ticks of that use. -/
@[ext] structure EClocked (X : Type u₁) (Y : Type u₂) where
  /-- The function. -/
  fn : X → Y
  /-- The expected number of uses of the input for one use of the output. -/
  uses : X → ℝ≥0
  /-- The expected clock ticks of one use of the output. -/
  cost : X → ℝ≥0

namespace EClocked

variable {X : Type u₁} {Y : Type u₂} {Z : Type u₃}

/-- The identity uses its input once and costs nothing. -/
protected def id (X : Type u₁) : EClocked X X where
  fn a := a
  uses _ := 1
  cost _ := 0

/-- The composite: the expected uses multiply, and the expected cost is the cost of `g` plus its
expected uses times the cost of `f`. -/
def comp (g : EClocked Y Z) (f : EClocked X Y) : EClocked X Z where
  fn a := g.fn (f.fn a)
  uses a := g.uses (f.fn a) * f.uses a
  cost a := g.cost (f.fn a) + g.uses (f.fn a) * f.cost a

/-- The expected demand of a data token (`false`) and of a clock tick (`true`). -/
noncomputable def eBack (n c : ℝ≥0) : Bool → (Bool →₀ ℝ≥0)
  | false => n • Finsupp.single false 1 + c • Finsupp.single true 1
  | true => Finsupp.single true 1

/-- The morphism with expected demands of a costed function with expected use counts: a data token
demands `uses` data tokens and `cost` ticks in expectation, a tick one tick. -/
noncomputable def toEDN (h : EClocked X Y) : EDNLens (clockPos X) (clockPos Y) where
  toFunA := h.fn
  toFunB a := eBack (h.uses a) (h.cost a)

/-- The morphism of the identity is the identity. -/
theorem toEDN_id : toEDN (EClocked.id X) = EDNLens.id (clockPos X) := by
  refine EDNLens.ext (fun _ => rfl) fun a b => ?_
  cases b <;> simp [toEDN, eBack, EClocked.id, EDNLens.id]

/-- The morphism of a composite is the composite: expected uses `n₂ * n₁`, expected ticks
`c₂ + n₂ * c₁`. -/
theorem toEDN_comp (g : EClocked Y Z) (f : EClocked X Y) :
    toEDN (comp g f) = EDNLens.comp (toEDN g) (toEDN f) := by
  refine EDNLens.ext (fun _ => rfl) fun a b => ?_
  cases b
  · ext b'
    cases b' <;>
      simp [toEDN, EDNLens.comp, eBack, comp, Finsupp.linearCombination_single,
        mul_comm, add_comm]
  · simp [toEDN, EDNLens.comp, eBack, comp, Finsupp.linearCombination_single]

/-- The expected time of one use of the output of `h` at `a` when one use of the input takes
expected time `T`. -/
def time (h : EClocked X Y) (T : ℝ≥0) (a : X) : ℝ≥0 :=
  h.cost a + h.uses a * T

/-- The price of the tokens at which a data token costs `T` and a tick one unit. -/
def timePrice (T : ℝ≥0) : ∀ _ : X, Bool → ℝ≥0 :=
  fun _ b => bif b then 1 else T

/-- The expected time is the price of a data token of the morphism. -/
theorem time_eq_price (h : EClocked X Y) (T : ℝ≥0) (a : X) :
    h.time T a = (toEDN h).price (timePrice T) a false := by
  simp [time, EDNLens.price, toEDN, eBack, timePrice, Finsupp.linearCombination_single,
    add_comm, mul_comm]

/-- The price of a tick is one unit. -/
theorem price_toEDN_true (h : EClocked X Y) (T : ℝ≥0) (a : X) :
    (toEDN h).price (timePrice T) a true = 1 := by
  simp [EDNLens.price, toEDN, eBack, timePrice, Finsupp.linearCombination_single]

/-- **The expected time of a composite** is the expected time of `g` at the expected time of `f`:
the price of the composite morphism is the price under `g` of the price under `f`. -/
theorem time_comp (g : EClocked Y Z) (f : EClocked X Y) (T : ℝ≥0) (a : X) :
    (comp g f).time T a = g.time (f.time T a) (f.fn a) := by
  rw [time_eq_price, toEDN_comp, EDNLens.price_comp, time_eq_price g]
  change Finsupp.linearCombination ℝ≥0 _ (eBack (g.uses (f.fn a)) (g.cost (f.fn a)) false) =
    Finsupp.linearCombination ℝ≥0 _ (eBack (g.uses (f.fn a)) (g.cost (f.fn a)) false)
  congr 2
  funext b
  cases b
  · exact (time_eq_price f T a).symm
  · exact price_toEDN_true f T a

/-- The expected time is monotone in the expected time of a use of the input. -/
theorem time_mono (h : EClocked X Y) {T T' : ℝ≥0} (hT : T ≤ T') (a : X) :
    h.time T a ≤ h.time T' a := by
  unfold time
  gcongr

end EClocked

/-! ## A rewinding loop with geometric retries -/

/-- The rewinding loop with retries: a trial repeated until it succeeds, each trial succeeding
with probability `p`, at the cost `c` of the loop per trial. Its result is that of the successful
trial; it uses the trial `p⁻¹` times in expectation (`expected_trials_geometric`) and costs `c` per
trial. -/
noncomputable def retryClocked (X : Type u₁) (p c : ℝ≥0) : EClocked X X where
  fn a := a
  uses _ := p⁻¹
  cost _ := c * p⁻¹

/-- **The expected number of trials** of the loop is the mean of the number of trials until the
first success, `N + 1` for `N` geometric with parameter `p`: the masses `(1 - p) ^ n * p` of a
success at trial `n + 1` sum to one, and their mean is the expected uses of the loop. -/
theorem expected_trials_geometric (X : Type u₁) {p : ℝ≥0} (c : ℝ≥0) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (a : X) :
    ∑' n : ℕ, (1 - (p : ℝ)) ^ n * p = 1 ∧
      (((retryClocked X p c).uses a : ℝ≥0) : ℝ) =
        ∑' n : ℕ, ((n : ℝ) + 1) * ((1 - (p : ℝ)) ^ n * p) := by
  have h0 : (0 : ℝ) < p := by exact_mod_cast hp0
  have h1 : (p : ℝ) ≤ 1 := by exact_mod_cast hp1
  refine ⟨tsum_geometric_mul_self h0 h1, ?_⟩
  rw [tsum_succ_mul_geometric_mul h0 h1]
  simp [retryClocked]

/-- The expected time of the loop at a trial of expected time `T`: `(c + T) / p`. -/
theorem retryClocked_time (X : Type u₁) (p c T : ℝ≥0) (a : X) :
    (retryClocked X p c).time T a = (c + T) * p⁻¹ := by
  simp only [EClocked.time, retryClocked]
  ring

/-- **The expected-time certificate of the loop around a trial** `f`: the loop runs `f` afresh at
each trial, and its expected time is `(c + f.time T a) / p`, the composition law of expected
demands at the trial. -/
theorem retryClocked_comp_time {X : Type u₁} {Y : Type u₂} (f : EClocked X Y) (p c T : ℝ≥0)
    (a : X) :
    (EClocked.comp (retryClocked Y p c) f).time T a = (c + f.time T a) * p⁻¹ := by
  rw [EClocked.time_comp, retryClocked_time]

/-- At a success probability of at least `ε > 0`, the loop uses the trial at most `ε⁻¹` times in
expectation and takes at most `(c + T) / ε`. -/
theorem retryClocked_time_le (X : Type u₁) {p ε : ℝ≥0} (c T : ℝ≥0) (hε : 0 < ε) (hεp : ε ≤ p)
    (a : X) : (retryClocked X p c).uses a ≤ ε⁻¹ ∧ (retryClocked X p c).time T a ≤ (c + T) * ε⁻¹ := by
  have h : p⁻¹ ≤ ε⁻¹ := inv_anti₀ hε hεp
  refine ⟨h, ?_⟩
  rw [retryClocked_time]
  exact mul_le_mul_of_nonneg_left h zero_le

end CatCrypt.Container
