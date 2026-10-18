/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signatures.EUFCMA
public import CatCryptCore.Crypto.OracleAdversary

/-!
# The EUF-CMA game for signature schemes given by probability mass functions

A signature scheme `PSigScheme` whose key generation is a function of uniform
coins and whose signing algorithm is a probability mass function defines a
`SigScheme` with heap-independent algorithms (`PSigScheme.toSigScheme`). An
adaptive oracle adversary `B : PK → OracleAdv Msg Sig (Msg × Sig)` defines an
EUF-CMA adversary (`toEUFAdversary B`) whose coin flips are heap-independent
steps. For these, the EUF-CMA advantage is the probability of `true` in the
distribution `eufDist S B`: sample the key coins, run `B` on the public key
against the signing oracle `signOracle S sk`, which appends every query and its
answer to a list, and check that the output verifies and its message is not in
the list.

## Main definitions

* `PSigScheme` — a signature scheme with coin-based key generation and
  distribution-valued signing
* `PSigScheme.keyDist` — the key distribution, key generation applied to uniform coins
* `PSigScheme.Deterministic` — signing is a point mass at a signing function `dsign`
* `liftPMF` — a probability mass function as a heap-independent computation
* `OracleAdv.toProg` — an adaptive oracle adversary as an oracle program
* `signOracle` — the logging signing oracle on lists
* `eufDist` — the output distribution of the EUF-CMA game

## Main results

* `eufcmaAdvantage_toEUFAdversary` — the EUF-CMA advantage of `toEUFAdversary B`
  against `S.toSigScheme` is `eufDist S B true`
* `run_query_signOracle_det` — against a deterministic scheme, a signing query on `m`
  answers `dsign sk m`
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

namespace CatCrypt.Crypto.Signatures

/-- A signature scheme with key generation from uniform coins `KR` and signing
given by a probability mass function. -/
structure PSigScheme (Msg PK SK Sig : Type) : Type 1 where
  /-- Key generation coins. -/
  KR : Type
  [finKR : Fintype KR]
  [neKR : Nonempty KR]
  /-- Key generation from coins. -/
  keygen : KR → PK × SK
  /-- Signing. -/
  sign : SK → Msg → PMF Sig
  /-- Verification. -/
  verify : PK → Msg → Sig → Bool

attribute [instance] PSigScheme.finKR PSigScheme.neKR

/-- A probability mass function as a computation that leaves the heap unchanged. -/
noncomputable def liftPMF {α : Type} (p : PMF α) : SPComp α :=
  fun h => p.map fun a => some (a, h)

theorem sdistr_bind_map_some {α β γ : Type} (p : PMF α) (g : α → β) (F : β → SDistr γ) :
    SDistr.bind (p.map fun a => some (g a)) F = p.bind fun a => F (g a) := by
  unfold SDistr.bind
  rw [PMF.bind_map]
  rfl

theorem liftPMF_bind_apply {α β : Type} (p : PMF α) (f : α → SPComp β) (h : Heap) :
    SPComp.bind (liftPMF p) f h = p.bind fun a => f a h := by
  unfold SPComp.bind liftPMF
  exact sdistr_bind_map_some p (fun a => (a, h)) _

variable {Msg PK SK Sig : Type}

/-- The signature scheme with heap-independent algorithms defined by `S`. -/
noncomputable def PSigScheme.toSigScheme (S : PSigScheme Msg PK SK Sig) :
    SigScheme Msg PK SK Sig where
  keygen := liftPMF ((PMF.uniformOfFintype S.KR).map S.keygen)
  sign sk m := liftPMF (S.sign sk m)
  verify := S.verify

/-- The key distribution of `S`: key generation applied to uniform coins. -/
noncomputable def PSigScheme.keyDist (S : PSigScheme Msg PK SK Sig) : PMF (PK × SK) :=
  (PMF.uniformOfFintype S.KR).map S.keygen

/-- The key generation of `S.toSigScheme` samples from `S.keyDist`. -/
theorem PSigScheme.toSigScheme_keygen (S : PSigScheme Msg PK SK Sig) :
    S.toSigScheme.keygen = liftPMF S.keyDist := rfl

/-- A deterministic signature scheme: signing `m` under `sk` returns `dsign sk m` with
probability one. -/
class PSigScheme.Deterministic (S : PSigScheme Msg PK SK Sig) where
  /-- The signing function. -/
  dsign : SK → Msg → Sig
  /-- Signing is the point mass at `dsign`. -/
  sign_eq : ∀ sk m, S.sign sk m = PMF.pure (dsign sk m)

/-- An adaptive oracle adversary as an oracle program: coin flips become
heap-independent steps. -/
noncomputable def _root_.CatCrypt.Crypto.OracleAdv.toProg {I O α : Type} :
    OracleAdv I O α → OracleProg I O α
  | .ret a => .pure a
  | .rand p k => .lift (liftPMF p) fun b => OracleAdv.toProg (k b)
  | .query i k => .query i fun o => OracleAdv.toProg (k o)

/-- The signing oracle with key `sk` on a list of previous queries and answers:
it signs `m` and appends `(m, σ)`. -/
noncomputable def signOracle (S : PSigScheme Msg PK SK Sig) (sk : SK) :
    List (Msg × Sig) → Msg → PMF (Sig × List (Msg × Sig)) :=
  fun l m => (S.sign sk m).map fun σ => (σ, l ++ [(m, σ)])

/-- The signing oracle of a deterministic scheme answers `dsign sk m` and appends
`(m, dsign sk m)`. -/
theorem signOracle_det (S : PSigScheme Msg PK SK Sig) [hS : S.Deterministic] (sk : SK)
    (l : List (Msg × Sig)) (m : Msg) :
    signOracle S sk l m = PMF.pure (hS.dsign sk m, l ++ [(m, hS.dsign sk m)]) := by
  rw [signOracle, hS.sign_eq, PMF.pure_map]

/-- A signing query of a deterministic scheme answers `dsign sk m`, and the run
continues from the list extended by `(m, dsign sk m)`. -/
@[simp] theorem run_query_signOracle_det (S : PSigScheme Msg PK SK Sig) [hS : S.Deterministic]
    (sk : SK) {α : Type} (m : Msg) (k : Sig → OracleAdv Msg Sig α) (l : List (Msg × Sig)) :
    OracleAdv.run (signOracle S sk) (.query m k) l =
      OracleAdv.run (signOracle S sk) (k (hS.dsign sk m)) (l ++ [(m, hS.dsign sk m)]) := by
  rw [OracleAdv.run_query, signOracle_det, PMF.pure_bind]

/-- A run against the signing oracle from the list `l₀` is the run from the empty
list with `l₀` prepended. -/
theorem run_signOracle_shift (S : PSigScheme Msg PK SK Sig) (sk : SK) {α : Type}
    (B : OracleAdv Msg Sig α) (l₀ : List (Msg × Sig)) :
    OracleAdv.run (signOracle S sk) B l₀ =
      (OracleAdv.run (signOracle S sk) B []).map fun x => (x.1, l₀ ++ x.2) := by
  induction B generalizing l₀ with
  | ret a => simp [PMF.pure_map]
  | rand p k ih =>
    simp only [OracleAdv.run_rand, PMF.map_bind]
    exact congrArg _ (funext fun b => ih b l₀)
  | query m k ih =>
    have e : ∀ l, signOracle S sk l m = (S.sign sk m).map fun σ => (σ, l ++ [(m, σ)]) :=
      fun _ => rfl
    rw [OracleAdv.run_query, OracleAdv.run_query, e, e, PMF.bind_map, PMF.bind_map,
      PMF.map_bind]
    refine congrArg _ (funext fun σ => ?_)
    simp only [Function.comp_apply]
    rw [ih σ (l₀ ++ [(m, σ)]), ih σ ([] ++ [(m, σ)]), PMF.map_comp]
    congr 1
    funext x
    simp

/-- The logged run of the oracle program of `B` against the signing algorithm is
the run of `B` against the signing oracle, at every heap. -/
theorem runLog_toProg (S : PSigScheme Msg PK SK Sig) (sk : SK) {α : Type}
    (B : OracleAdv Msg Sig α) (h : Heap) :
    (B.toProg.runLog fun m => liftPMF (S.sign sk m)) h =
      (OracleAdv.run (signOracle S sk) B []).map fun x => some (x, h) := by
  induction B with
  | ret a => simp [OracleAdv.toProg, OracleProg.runLog, SPComp.pure, SDistr.pure, PMF.pure_map]
  | rand p k ih =>
    simp only [OracleAdv.toProg, OracleProg.runLog, OracleProg.runWith_lift] at ih ⊢
    rw [liftPMF_bind_apply, OracleAdv.run_rand, PMF.map_bind]
    exact congrArg _ (funext ih)
  | query m k ih =>
    simp only [OracleAdv.toProg, OracleProg.runLog, OracleProg.runWith_query,
      OracleProg.logging] at ih ⊢
    rw [SPComp.bind_assoc, liftPMF_bind_apply]
    simp only [SPComp.pure_bind]
    have e : signOracle S sk [] m = (S.sign sk m).map fun σ => (σ, [] ++ [(m, σ)]) := rfl
    rw [OracleAdv.run_query, e, PMF.bind_map, PMF.map_bind]
    refine congrArg _ (funext fun σ => ?_)
    simp only [Function.comp_apply]
    rw [SPComp.bind_def, ih σ, sdistr_bind_map_some,
      run_signOracle_shift S sk (k σ) ([] ++ [(m, σ)]), PMF.map_comp]
    simp only [SPComp.pure, SDistr.pure]
    rw [← PMF.bind_pure_comp]
    rfl

/-- The EUF-CMA adversary running `B`. -/
noncomputable def toEUFAdversary (B : PK → OracleAdv Msg Sig (Msg × Sig)) :
    EUFCMAAdversary Msg PK SK Sig :=
  ⟨fun pk => (B pk).toProg⟩

/-- The output distribution of the EUF-CMA game for `S` and `B`. -/
noncomputable def eufDist [DecidableEq Msg] (S : PSigScheme Msg PK SK Sig)
    (B : PK → OracleAdv Msg Sig (Msg × Sig)) : PMF Bool :=
  (PMF.uniformOfFintype S.KR).bind fun kr =>
    (OracleAdv.run (signOracle S (S.keygen kr).2) (B (S.keygen kr).1) []).map fun x =>
      S.verify (S.keygen kr).1 x.1.1 x.1.2 && !(x.2.map Prod.fst).contains x.1.1

theorem prTrue_liftPMF (p : PMF Bool) (h₀ : Heap) : prTrue (liftPMF p) h₀ = p true := by
  unfold prTrue liftPMF
  simp only [PMF.map_apply]
  rw [ENNReal.tsum_comm]
  rw [tsum_eq_single true (fun b hb => by
    refine ENNReal.tsum_eq_zero.mpr fun h => ?_
    simp [Ne.symm hb])]
  rw [tsum_eq_single h₀ (fun h hh => by simp [hh])]
  simp

/-- **EUF-CMA advantage of an adaptive oracle adversary.** The EUF-CMA advantage
of `toEUFAdversary B` against `S.toSigScheme` is the probability of `true` in
`eufDist S B`. -/
theorem eufcmaAdvantage_toEUFAdversary [DecidableEq Msg] (S : PSigScheme Msg PK SK Sig)
    (B : PK → OracleAdv Msg Sig (Msg × Sig)) :
    eufcmaAdvantage S.toSigScheme (toEUFAdversary B) = eufDist S B true := by
  have hgame : eufcmaGame S.toSigScheme (toEUFAdversary B) = liftPMF (eufDist S B) := by
    funext h
    unfold eufcmaGame
    change SPComp.bind (liftPMF ((PMF.uniformOfFintype S.KR).map S.keygen)) _ h = _
    rw [liftPMF_bind_apply, PMF.bind_map]
    change _ = (eufDist S B).map _
    unfold eufDist
    rw [PMF.map_bind]
    refine congrArg _ (funext fun kr => ?_)
    simp only [Function.comp_apply]
    rw [SPComp.bind_def]
    change SDistr.bind ((((B (S.keygen kr).1).toProg).runLog
      fun m => liftPMF (S.sign (S.keygen kr).2 m)) h) _ = _
    rw [runLog_toProg, sdistr_bind_map_some, PMF.map_comp]
    simp only [SPComp.pure, SDistr.pure]
    rw [← PMF.bind_pure_comp]
    rfl
  unfold eufcmaAdvantage
  rw [hgame, prTrue_liftPMF]

end CatCrypt.Crypto.Signatures
