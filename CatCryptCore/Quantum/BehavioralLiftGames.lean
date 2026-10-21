/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.BehavioralLift
public import CatCryptCore.Crypto.Assumptions.AEAD
public import CatCryptCore.Crypto.ForkingLemma

/-!
# One-shot games and prefix reductions as oracle trees

Classical games that sample a challenge and call the distinguisher once, written as oracle
trees with one call, so that `qGap_le_of_cGap_le_of_isQueryBound_one` lifts a classical
per-distinguisher bound to quantum distinguishers with a classical interface. Two shapes are
covered: a heap-independent `SPComp` game followed by the distinguisher (`oneShotTree`), and
a PRF or PRP game against an oracle adversary that runs a prefix and then samples the output
bit of the distinguisher on the prefix's result (`pmfShotTree` of `prfRealD`, `rfD`, `rpD`).

## Main definitions

* `valD c`: the output sub-distribution of a computation run from the empty heap
* `oneShotTree μ`: the oracle tree sampling a challenge from `μ`, calling the distinguisher
  on it and outputting its bit
* `pmfShotTree p`: the same tree for a challenge distribution `p : PMF X`
* `prfRealD F R`, `rfD R`, `rpD R`: the output distribution of the oracle adversary `R` run
  against `F k` under a uniform key, against the lazily sampled random function, and against
  the lazily sampled random injection

## Main results

* `prTrue_bind_ofSDistrAdv_eq_outRunD`: a heap-independent game `c` against the classical
  sampling distinguisher `ofSDistrAdv f` is the run of `oneShotTree (valD c)` against `f`
* `prTrue_realGame_bind`, `prTrue_rfGame_bind`, `prTrue_rpGame_bind`: the PRF and PRP games
  of `R.bind fun a => .rand (g a) .ret` output `true` with the weight of `g` under the output
  distribution of `R`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CatCrypt.Quantum

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.PRPPRF (realGame rfGame rpGame keyedOracle rfOracle rpOracle)
open scoped ENNReal

/-! ## Heap-independent games followed by one call -/

section OneShot

variable {X X' : Type}

/-- The output sub-distribution of `c` run from the empty heap. -/
def valD (c : SPComp X) : SDistr X :=
  (c Heap.empty).bind fun r => SDistr.pure r.1

/-- A heap-independent computation samples its output from `valD c` and leaves the heap
unchanged. -/
theorem eq_bind_valD {c : SPComp X} (hc : SPComp.IsPure c) (h : Heap) :
    c h = (valD c).bind fun a => SDistr.pure (a, h) := by
  obtain ⟨μ, hμ⟩ := hc
  have hv : valD c = μ := by
    simp only [valD, hμ, SDistr.bind_assoc, SDistr.pure_bind, SDistr.bind_pure]
  rw [hv, hμ]

/-- The one-shot game tree: sample a challenge from `μ`, call the distinguisher on it, and
output its bit. -/
def oneShotTree (μ : SDistr X) : OracleAdv X Bool Bool :=
  bindD μ fun x => .query x .ret

theorem isQueryBound_oneShotTree (μ : SDistr X) : (oneShotTree μ).IsQueryBound 1 :=
  isQueryBound_bindD fun _ _ => trivial

/-- The probability that the classical sampling distinguisher `ofSDistrAdv f` outputs `true`
is the weight of `true` under `f x`. -/
theorem prTrue_ofSDistrAdv (f : X → SDistr Bool) (x : X) (h : Heap) :
    prTrue (ofSDistrAdv f x) h = f x (some true) := by
  rw [← SPComp.bind_pure (ofSDistrAdv f x),
    prTrue_bind_of_eq_bind (c := ofSDistrAdv f x) (fun _ => rfl)]
  simp only [CatCrypt.Crypto.ForkingLemma.prTrue_pure_bool, tsum_bool]
  simp

/-- A heap-independent game followed by the classical sampling distinguisher `f ∘ g`. -/
theorem prTrue_bind_ofSDistrAdv {c : SPComp X'} (hc : SPComp.IsPure c) (g : X' → X)
    (f : X → SDistr Bool) :
    prTrue (c.bind fun x => ofSDistrAdv f (g x)) Heap.empty =
      ∑' x, valD c (some x) * f (g x) (some true) := by
  rw [prTrue_bind_of_eq_bind (eq_bind_valD hc)]
  simp only [prTrue_ofSDistrAdv]

/-- The one-shot tree with each call `x` answered by one call at `g x`. -/
theorem outRunD_substQ_oneShotTree (μ : SDistr X') (g : X' → X) (f : X → SDistr Bool) :
    OracleAdv.outRunD (statelessOracle f)
        (OracleAdv.substQ (fun x => .query (g x) .ret) (oneShotTree μ)) () (some true) =
      ∑' x, μ (some x) * f (g x) (some true) := by
  rw [oneShotTree, substQ_bindD, outRunD_bindD_true]
  refine tsum_congr fun x => congrArg _ ?_
  simp only [OracleAdv.substQ, OracleAdv.bind]
  rw [outRunD_statelessOracle_query, tsum_bool]
  simp [OracleAdv.outRunD_ret, SDistr.pure_apply_some]

theorem isQueryBound_substQ_oneShotTree (μ : SDistr X') (g : X' → X) :
    (OracleAdv.substQ (fun x => .query (g x) .ret) (oneShotTree μ) :
      OracleAdv X Bool Bool).IsQueryBound 1 := by
  rw [oneShotTree, substQ_bindD]
  exact isQueryBound_bindD fun _ _ => trivial

theorem outRunD_oneShotTree (μ : SDistr X) (f : X → SDistr Bool) :
    OracleAdv.outRunD (statelessOracle f) (oneShotTree μ) () (some true) =
      ∑' x, μ (some x) * f x (some true) := by
  rw [oneShotTree, outRunD_bindD_true]
  refine tsum_congr fun x => congrArg _ ?_
  rw [outRunD_statelessOracle_query, tsum_bool]
  simp [OracleAdv.outRunD_ret, SDistr.pure_apply_some]

/-- The game `c` against the classical sampling distinguisher `f` is the one-shot tree of
`valD c` run against `f`. -/
theorem prTrue_bind_ofSDistrAdv_eq_outRunD {c : SPComp X} (hc : SPComp.IsPure c)
    (f : X → SDistr Bool) :
    prTrue (c.bind (ofSDistrAdv f)) Heap.empty =
      OracleAdv.outRunD (statelessOracle f) (oneShotTree (valD c)) () (some true) := by
  rw [outRunD_oneShotTree]
  exact prTrue_bind_ofSDistrAdv hc id f

end OneShot

/-! ## Oracle adversaries that run a prefix and then sample the output bit -/

section Prefix

variable {X D Rg : Type}

/-- The one-shot game tree: sample a challenge from `p`, call the distinguisher on it, and
output its bit. -/
def pmfShotTree (p : PMF X) : OracleAdv X Bool Bool :=
  .rand p fun x => .query x .ret

theorem isQueryBound_pmfShotTree (p : PMF X) : (pmfShotTree p).IsQueryBound 1 :=
  fun _ _ => trivial

theorem outRunD_pmfShotTree (p : PMF X) (f : X → SDistr Bool) :
    OracleAdv.outRunD (statelessOracle f) (pmfShotTree p) () (some true) =
      ∑' x, p x * f x (some true) := by
  rw [pmfShotTree, OracleAdv.outRunD_rand, sdistr_bind_apply_some]
  refine tsum_congr fun x => ?_
  rw [pmf_map_some_apply, outRunD_statelessOracle_query, tsum_bool]
  simp [OracleAdv.outRunD_ret, SDistr.pure_apply_some]

/-- Running `R` followed by a sample of `g` on its output, the output marginal is the output
marginal of `R` followed by `g`. -/
theorem run_bind_rand_map_fst {S : Type} (O : S → D → PMF (Rg × S)) (R : OracleAdv D Rg X)
    (g : X → PMF Bool) (s : S) :
    (OracleAdv.run O (R.bind fun a => .rand (g a) .ret) s).map Prod.fst =
      ((OracleAdv.run O R s).map Prod.fst).bind g := by
  rw [OracleAdv.run_bind, PMF.map_bind, PMF.bind_map]
  refine congrArg _ (funext fun r => ?_)
  simp only [OracleAdv.run_rand, OracleAdv.run_ret, PMF.map_bind, PMF.pure_map]
  exact PMF.bind_pure _

/-- The output distribution of the oracle adversary `R` run against the lazily sampled random
function. -/
def rfD [DecidableEq D] [Fintype Rg] [Nonempty Rg] (R : OracleAdv D Rg X) : PMF X :=
  (OracleAdv.run rfOracle R []).map Prod.fst

/-- The output distribution of the oracle adversary `R` run against the lazily sampled random
injection. -/
def rpD [DecidableEq D] [DecidableEq Rg] [Fintype Rg] [Nonempty Rg] (R : OracleAdv D Rg X) :
    PMF X :=
  (OracleAdv.run rpOracle R []).map Prod.fst

theorem prTrue_rfGame_bind [DecidableEq D] [Fintype Rg] [Nonempty Rg] (R : OracleAdv D Rg X)
    (g : X → PMF Bool) :
    prTrue (rfGame (R.bind fun a => .rand (g a) .ret)) Heap.empty =
      ∑' x, rfD R x * g x true := by
  rw [rfGame, prTrue_liftPMF, run_bind_rand_map_fst, PMF.bind_apply]
  rfl

theorem prTrue_rpGame_bind [DecidableEq D] [DecidableEq Rg] [Fintype Rg] [Nonempty Rg]
    (R : OracleAdv D Rg X) (g : X → PMF Bool) :
    prTrue (rpGame (R.bind fun a => .rand (g a) .ret)) Heap.empty =
      ∑' x, rpD R x * g x true := by
  rw [rpGame, prTrue_liftPMF, run_bind_rand_map_fst, PMF.bind_apply]
  rfl

variable {K : Type} [Fintype K] [Nonempty K]

/-- The output distribution of the oracle adversary `R` run against `F k` under a uniform
key `k`. -/
def prfRealD (F : K → D → Rg) (R : OracleAdv D Rg X) : PMF X :=
  (PMF.uniformOfFintype K).bind fun k => (OracleAdv.run (keyedOracle F k) R ()).map Prod.fst

theorem prTrue_realGame_bind (F : K → D → Rg) (R : OracleAdv D Rg X) (g : X → PMF Bool) :
    prTrue (realGame F (R.bind fun a => .rand (g a) .ret)) Heap.empty =
      ∑' x, prfRealD F R x * g x true := by
  rw [realGame, prTrue_liftPMF]
  simp only [run_bind_rand_map_fst, ← PMF.bind_bind]
  rw [PMF.bind_apply]
  rfl

end Prefix

end CatCrypt.Quantum
