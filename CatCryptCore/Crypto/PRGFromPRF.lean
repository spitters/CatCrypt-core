/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PRPPRFSwitching
public import CatCryptCore.Crypto.Assumptions.OWF
public import CatCryptCore.Tactics.DeriveTimed

/-!
# A PRG from a PRF at two distinct points

For a keyed function `F : K → B → Y` and two distinct points `b₁ ≠ b₂`, the generator
`twoPointPRG F b₁ b₂` stretches a key `k` to `(F k b₁, F k b₂)`. Its real PRG game is the real
world of the adaptive PRF game against the two-query distinguisher `twoPointRed b₁ b₂ A`, and,
since the two points differ, its ideal PRG game is the random-function world of that game.

## Main definitions

* `twoPointPRG F b₁ b₂` — the generator `k ↦ (F k b₁, F k b₂)`
* `twoPointRed b₁ b₂ A` — the PRF distinguisher: query `b₁` and `b₂`, run `A` on the answers

## Main results

* `prg_advantage_twoPointPRG_eq` — the PRG advantage of `A` is the adaptive PRF advantage of
  `twoPointRed b₁ b₂ A`
* `prg_advantage_twoPointPRG_le` — the same as an inequality
* `isQueryBound_twoPointRed` — the reduction asks two queries
* `twoPointRed.timeBound_timed` — the reduction runs in the time of `A` plus a constant

## References

* O. Goldreich, S. Goldwasser, S. Micali, *How to Construct Random Functions*, J. ACM 1986
* M. Rosulek, *The Joy of Cryptography*, Claim 6.3
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.PRGFromPRF

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.PRPPRF
open scoped ENNReal

variable {K B Y : Type}

/-- The generator stretching a key `k` to the values of `F k` at `b₁` and at `b₂`. -/
def twoPointPRG (F : K → B → Y) (b₁ b₂ : B) : Assumptions.PRGDef K (Y × Y) :=
  ⟨fun k => (F k b₁, F k b₂)⟩

/-- The output bit of a run of a Boolean computation: `b` for `some (b, h)`, and `false` for a
failed run. -/
def runBit : Option (Bool × Heap) → Bool
  | some (b, _) => b
  | none => false

/-- The adaptive PRF distinguisher built from a PRG adversary `A` on pairs: query the oracle at
`b₁` and at `b₂`, run `A` on the two answers from the empty heap and return its output bit. -/
noncomputable def twoPointRed (b₁ b₂ : B) (A : Assumptions.PRG_Adversary (Y × Y)) :
    OracleAdv B Y Bool :=
  .query b₁ fun y₁ => .query b₂ fun y₂ =>
    .rand (A (y₁, y₂) Heap.empty) fun o => .ret (runBit o)

/-- The reduction asks two queries. -/
theorem isQueryBound_twoPointRed (b₁ b₂ : B) (A : Assumptions.PRG_Adversary (Y × Y)) :
    (twoPointRed b₁ b₂ A).IsQueryBound 2 := by
  simp [twoPointRed, OracleAdv.IsQueryBound]

/-- The probability that `runBit` is `true` is the probability of a run ending with output
`true`, summed over final heaps. -/
theorem map_runBit_apply_true (p : PMF (Option (Bool × Heap))) :
    (p.map runBit) true = ∑' h, p (some (true, h)) := by
  rw [PMF.map_apply, SDistr.tsum_option_eq_add, ENNReal.tsum_prod', tsum_fintype,
    Fintype.sum_bool]
  simp [runBit]

/-- Recording the output bit together with a final oracle state and projecting the state away
is `map runBit`. -/
theorem map_fst_bind_runBit {σ : Type} (p : PMF (Option (Bool × Heap))) (t : σ) :
    (p.bind fun o => PMF.pure (runBit o, t)).map Prod.fst = p.map runBit := by
  rw [PMF.map_bind]
  simp only [PMF.pure_map]
  exact PMF.bind_pure_comp _ _

variable [Fintype K] [Nonempty K]

/-- The real adaptive PRF game against `twoPointRed b₁ b₂ A` accepts with the probability of
the real PRG game of `twoPointPRG F b₁ b₂` against `A`. -/
theorem prTrue_realGame_twoPointRed (F : K → B → Y) (b₁ b₂ : B)
    (A : Assumptions.PRG_Adversary (Y × Y)) :
    prTrue (realGame F (twoPointRed b₁ b₂ A)) Heap.empty =
      prTrue ((Assumptions.prg_real (twoPointPRG F b₁ b₂)).bind A) Heap.empty := by
  rw [realGame, prTrue_liftPMF]
  simp only [Assumptions.prg_real, SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind,
    prTrue_bind_sample]
  rw [PMF.bind_apply, tsum_fintype]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [PMF.uniformFintype_apply, twoPointRed, OracleAdv.run_query, OracleAdv.run_rand,
    OracleAdv.run_ret, keyedOracle, PMF.pure_bind, map_fst_bind_runBit, map_runBit_apply_true]
  rfl

variable [Fintype Y] [Nonempty Y] [DecidableEq B]

/-- The random-function adaptive PRF game against `twoPointRed b₁ b₂ A` accepts with the
probability of the ideal PRG game on pairs against `A`, since the points `b₁` and `b₂`
differ. -/
theorem prTrue_rfGame_twoPointRed {b₁ b₂ : B} (hb : b₁ ≠ b₂)
    (A : Assumptions.PRG_Adversary (Y × Y)) :
    prTrue (rfGame (twoPointRed b₁ b₂ A)) Heap.empty =
      prTrue ((Assumptions.prg_ideal (Output := Y × Y)).bind A) Heap.empty := by
  have hne : (b₂ == b₁) = false := by simpa using Ne.symm hb
  rw [rfGame, prTrue_liftPMF]
  simp only [twoPointRed, rfOracle, OracleAdv.run_query, OracleAdv.run_rand, OracleAdv.run_ret,
    List.lookup_nil, List.lookup_cons, hne, PMF.bind_map, Function.comp_def, PMF.map_bind]
  simp only [PMF.pure_map, ← Function.comp_apply (f := PMF.pure) (g := runBit),
    PMF.bind_pure_comp]
  simp only [Assumptions.prg_ideal, SPComp.sample_prod_eq, SPComp.bind_assoc, SPComp.pure_bind,
    prTrue_bind_sample, PMF.bind_apply, tsum_fintype, PMF.uniformFintype_apply,
    ← Finset.mul_sum, map_runBit_apply_true]
  rfl

/-- **The two-point PRG advantage is an adaptive PRF advantage.** For `b₁ ≠ b₂` and every
adversary `A`, the PRG advantage of `A` against `k ↦ (F k b₁, F k b₂)` equals the adaptive PRF
advantage of `F` against the two-query reduction `twoPointRed b₁ b₂ A`. -/
theorem prg_advantage_twoPointPRG_eq (F : K → B → Y) {b₁ b₂ : B} (hb : b₁ ≠ b₂)
    (A : Assumptions.PRG_Adversary (Y × Y)) :
    Assumptions.PRG_Advantage (twoPointPRG F b₁ b₂) A =
      PRF_q_Advantage F (twoPointRed b₁ b₂ A) := by
  simp only [Assumptions.PRG_Advantage, AdvantageA, PRF_q_Advantage, Advantage,
    prTrue_realGame_twoPointRed, prTrue_rfGame_twoPointRed hb]

/-- **PRG from PRF at two points.** For `b₁ ≠ b₂` and every adversary `A`, the PRG advantage of
`A` against `k ↦ (F k b₁, F k b₂)` is at most the adaptive PRF advantage of `F` against the
two-query reduction `twoPointRed b₁ b₂ A`. -/
theorem prg_advantage_twoPointPRG_le (F : K → B → Y) {b₁ b₂ : B} (hb : b₁ ≠ b₂)
    (A : Assumptions.PRG_Adversary (Y × Y)) :
    Assumptions.PRG_Advantage (twoPointPRG F b₁ b₂) A ≤
      PRF_q_Advantage F (twoPointRed b₁ b₂ A) :=
  (prg_advantage_twoPointPRG_eq F hb A).le

/-! ## Costed reduction -/

derive_timed twoPointRed

omit [Fintype Y] [Nonempty Y] [DecidableEq B] in
open OracleAdv.Timed in
/-- **Time of the two-point reduction.** With the adversary `A` of cost at most `a` on every
pair, the costed reduction has time at most `8 + a`: two queries, the run of `A` and the
return of its output bit. -/
theorem twoPointRed.timeBound_timed (b₁ b₂ : B) (A : Assumptions.PRG_Adversary (Y × Y))
    (ACost : Y × Y → ℕ) {a : ℕ} (hA : ∀ y, ACost y ≤ a) :
    StepTimeBound (twoPointRed.timed b₁ b₂ A ACost) (8 + a) := by
  unfold twoPointRed.timed
  simp only [stepTimeBound_zero, TimeBound]
  grind

end CatCrypt.Crypto.PRGFromPRF
