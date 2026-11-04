/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PRPPRFSwitching
public import CatCryptCore.Crypto.Assumptions.OWF
public import CatCryptCore.Tactics.DeriveTimed
public import CatCryptCore.Crypto.Assumptions.ODH

/-!
# A PRG from a PRF at two distinct points

For a keyed function `F : K → B → Y` and two distinct points `b₁ ≠ b₂`, the generator
`twoPointPRG F b₁ b₂` stretches a key `k` to `(F k b₁, F k b₂)`. Its real PRG game is the real
world of the adaptive PRF game against the two-query distinguisher `twoPointRed b₁ b₂ A`, and,
since the two points differ, its ideal PRG game is the random-function world of that game.

## Main definitions

* `twoPointPRG F b₁ b₂` — the generator `k ↦ (F k b₁, F k b₂)`
* `twoPointRed b₁ b₂ A` — the PRF distinguisher: query `b₁` and `b₂`, run `A` on the answers
* `chainPRG F b₁ next` — `k ↦ (F k b₁, F k (next (F k b₁)))`, and `chainRed b₁ next A`, its
  two-query reduction to the adaptive PRF game of `F`

## Main results

* `prg_advantage_twoPointPRG_eq` — the PRG advantage of `A` is the adaptive PRF advantage of
  `twoPointRed b₁ b₂ A`
* `prg_advantage_twoPointPRG_le` — the same as an inequality
* `isQueryBound_twoPointRed` — the reduction asks two queries
* `twoPointRed.timeBound_timed` — the reduction runs in the time of `A` plus a constant
* `prg_advantage_chainPRG_le`, `chainRed.timeBound_timed` — the same for two chained points
* `prg_advantage_prod_le_avg` — the PRG advantage on a product seed is at most the average of
  the advantages with the second component fixed

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

/-- The generator stretching a key `k` to `y₁ = F k b₁` and `F k (next y₁)`: two evaluations
of `F`, the second at a point computed from the first output. -/
def chainPRG (F : K → B → Y) (b₁ : B) (next : Y → B) : Assumptions.PRGDef K (Y × Y) :=
  ⟨fun k => (F k b₁, F k (next (F k b₁)))⟩

/-- The adaptive PRF distinguisher built from a PRG adversary `A` on pairs: query the oracle at
`b₁`, then at `next y₁` for the answer `y₁`, run `A` on the two answers from the empty heap and
return its output bit. -/
noncomputable def chainRed (b₁ : B) (next : Y → B) (A : Assumptions.PRG_Adversary (Y × Y)) :
    OracleAdv B Y Bool :=
  .query b₁ fun y₁ => .query (next y₁) fun y₂ =>
    .rand (A (y₁, y₂) Heap.empty) fun o => .ret (runBit o)

/-- The chained reduction asks two queries. -/
theorem isQueryBound_chainRed (b₁ : B) (next : Y → B) (A : Assumptions.PRG_Adversary (Y × Y)) :
    (chainRed b₁ next A).IsQueryBound 2 := by
  simp [chainRed, OracleAdv.IsQueryBound]

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

/-! ## Two chained points -/

omit [Fintype Y] [Nonempty Y] [DecidableEq B] in
/-- The real adaptive PRF game against `chainRed b₁ next A` accepts with the probability of the
real PRG game of `chainPRG F b₁ next` against `A`. -/
theorem prTrue_realGame_chainRed (F : K → B → Y) (b₁ : B) (next : Y → B)
    (A : Assumptions.PRG_Adversary (Y × Y)) :
    prTrue (realGame F (chainRed b₁ next A)) Heap.empty =
      prTrue ((Assumptions.prg_real (chainPRG F b₁ next)).bind A) Heap.empty := by
  rw [realGame, prTrue_liftPMF]
  simp only [Assumptions.prg_real, SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind,
    prTrue_bind_sample]
  rw [PMF.bind_apply, tsum_fintype]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [PMF.uniformFintype_apply, chainRed, OracleAdv.run_query, OracleAdv.run_rand,
    OracleAdv.run_ret, keyedOracle, PMF.pure_bind, map_fst_bind_runBit, map_runBit_apply_true]
  rfl

/-- The random-function adaptive PRF game against `chainRed b₁ next A` accepts with the
probability of the ideal PRG game on pairs against `A`, since the second point `next y₁`
differs from `b₁` for every `y₁`. -/
theorem prTrue_rfGame_chainRed {b₁ : B} {next : Y → B} (hb : ∀ y, next y ≠ b₁)
    (A : Assumptions.PRG_Adversary (Y × Y)) :
    prTrue (rfGame (chainRed b₁ next A)) Heap.empty =
      prTrue ((Assumptions.prg_ideal (Output := Y × Y)).bind A) Heap.empty := by
  have hne : ∀ y, (next y == b₁) = false := fun y => by simpa using hb y
  rw [rfGame, prTrue_liftPMF]
  simp only [chainRed, rfOracle, OracleAdv.run_query, OracleAdv.run_rand, OracleAdv.run_ret,
    List.lookup_nil, List.lookup_cons, hne, PMF.bind_map, Function.comp_def, PMF.map_bind]
  simp only [PMF.pure_map, ← Function.comp_apply (f := PMF.pure) (g := runBit),
    PMF.bind_pure_comp]
  simp only [Assumptions.prg_ideal, SPComp.sample_prod_eq, SPComp.bind_assoc, SPComp.pure_bind,
    prTrue_bind_sample, PMF.bind_apply, tsum_fintype, PMF.uniformFintype_apply,
    ← Finset.mul_sum, map_runBit_apply_true]
  rfl

/-- **PRG from PRF at two chained points.** If `next y ≠ b₁` for every `y`, the PRG advantage
of every adversary `A` against `chainPRG F b₁ next` is at most the adaptive PRF advantage of
`F` against the two-query reduction `chainRed b₁ next A`. -/
theorem prg_advantage_chainPRG_le (F : K → B → Y) {b₁ : B} {next : Y → B}
    (hb : ∀ y, next y ≠ b₁) (A : Assumptions.PRG_Adversary (Y × Y)) :
    Assumptions.PRG_Advantage (chainPRG F b₁ next) A ≤
      PRF_q_Advantage F (chainRed b₁ next A) :=
  le_of_eq (by
    simp only [Assumptions.PRG_Advantage, AdvantageA, PRF_q_Advantage, Advantage,
      prTrue_realGame_chainRed, prTrue_rfGame_chainRed hb])

/-! ## Averaging over a component of the seed -/

section Average

variable {S X O : Type} [Fintype S] [Nonempty S] [Fintype X] [Nonempty X] [Fintype O]
  [Nonempty O]

/-- **Averaging a PRG game over a seed component.** For a generator `R` on seeds `(s, x)` and
every adversary `A`, the PRG advantage is at most the average over `x` of the advantage of `A`
between `R (s, x)` for a uniform `s` and a uniform output. -/
theorem prg_advantage_prod_le_avg (R : Assumptions.PRGDef (S × X) O)
    (A : Assumptions.PRG_Adversary O) :
    Assumptions.PRG_Advantage R A ≤
      ∑ x : X, (Fintype.card X : ℝ≥0∞)⁻¹ *
        AdvantageA ((SPComp.sample S).bind fun s => SPComp.pure (R.stretch (s, x)))
          Assumptions.prg_ideal A := by
  have hreal : (Assumptions.prg_real R).bind A = (SPComp.sample X).bind fun x =>
      ((SPComp.sample S).bind fun s => SPComp.pure (R.stretch (s, x))).bind A := by
    simp only [Assumptions.prg_real, SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
    rw [← SPComp.sample_bind_equiv (Equiv.prodComm X S)]
    simp only [SPComp.sample_prod_eq, SPComp.bind_assoc, SPComp.pure_bind, Equiv.prodComm_apply,
      Prod.swap_prod_mk]
  have hideal : (Assumptions.prg_ideal (Output := O)).bind A =
      (SPComp.sample X).bind fun _ => (Assumptions.prg_ideal (Output := O)).bind A := by
    funext h
    simp only [SPComp.bind, SPComp.sample, SDistr.bind_assoc, SDistr.pure_bind]
    exact (SDistr.uniform_bind_const _).symm
  unfold Assumptions.PRG_Advantage AdvantageA
  calc Advantage ((Assumptions.prg_real R).bind A) ((Assumptions.prg_ideal (Output := O)).bind A)
      = Advantage ((SPComp.sample X).bind fun x =>
          ((SPComp.sample S).bind fun s => SPComp.pure (R.stretch (s, x))).bind A)
        ((SPComp.sample X).bind fun _ => (Assumptions.prg_ideal (Output := O)).bind A) := by
        rw [hreal, ← hideal]
    _ ≤ _ := Assumptions.advantage_sample_bind_le_avg _ _

end Average

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

derive_timed chainRed

omit [Fintype K] [Nonempty K] [Fintype Y] [Nonempty Y] [DecidableEq B] in
open OracleAdv.Timed in
/-- **Time of the chained reduction.** With the second point `next` of cost at most `c` and the
adversary `A` of cost at most `a` on every pair, the costed reduction has time at most
`9 + c + a`: two queries, the computation of the second point, the run of `A` and the return of
its output bit. -/
theorem chainRed.timeBound_timed (b₁ : B) (next : Y → B) (nextCost : Y → ℕ) {c : ℕ}
    (hnext : ∀ y, nextCost y ≤ c) (A : Assumptions.PRG_Adversary (Y × Y))
    (ACost : Y × Y → ℕ) {a : ℕ} (hA : ∀ y, ACost y ≤ a) :
    StepTimeBound (chainRed.timed b₁ next nextCost A ACost) (9 + c + a) := by
  unfold chainRed.timed
  simp only [stepTimeBound_zero, TimeBound]
  grind


end CatCrypt.Crypto.PRGFromPRF
