/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.TLSSquareSigned
public import CatCryptCore.Crypto.AKE.X3DHSquareGDH
public import CatCryptCore.Crypto.OracleFlagCount

/-!
# The TLS 1.3 handshake square under the gap Diffie–Hellman assumption

`TLSSquare.tls_filt_realizesSim_oracleGame` bounds the distance between the filtered TLS protocol
and the simulator `tlsSim` running with `F_AKEImp … srvImp` by the advantage of an oracle
adversary between `filtGameK lazyKDF A` and `simGame A`. This module bounds that advantage, for
TLS over a prime-order group `G` (`tlsDHAlg G Sg trs`), by the probability of a bad event of the
simulated world, and that probability by gap Diffie–Hellman advantages of explicit reductions
plus a statistical collision term; with `TLSSquareSigned.advantage_real_filt_le` it gives the
square of the real protocol.

**Transcript injectivity.** `TrInj trs`: each transcript operation is injective in all its
arguments. Two sessions that are not partners have different stage inputs.

**The bad event** (`TBad`), a transition of the simulated world:
* `KeyHit`: the key-derivation table of the simulator's copy holds an external stage input
  (label `cap`, `sap`, `exp` at the transcript up to server Finished, or `res` at a transcript
  extending it by a client Finished) with the (EC)DHE value of a session whose key the
  functionality chose (`status = .completed`);
* `CollAt`: a `hello` draws a client share that a server session of the same protocol session,
  naming the client as its peer, already received by `srvRecv`. The simulator impersonated that
  server, so it completes exposed while the client completes with a key of the functionality.

**The reduction** `tlsGdhRed G Sg trs i B`, on the challenge `(X, Y)` with the decision oracle
`O`, runs `B` against `redO`, a copy of the simulated world in which the `i`-th client share
drawn by `hello` is `X`, every server session that receives `X` has the share `Y · g^v` for a
drawn `v`, the (EC)DHE values that need the secret of `X` are symbolic (`inr E` is `E^x`), and the
key-derivation table is compared with `O` (`X3DHSquareGDH.symEq`). It outputs `W · X^{-v}` for the
first table entry with a known value `W` and a recorded `v` that `O` accepts at `(X, Y · g^v, W)`
(`extractT`).

## Main definitions

* `TrInj`: injectivity of the transcript operations.
* `KeyHit`, `CollAt`, `TBad`, `badProb`, `keyProb`, `collProb`: the bad event and the
  probabilities of its two parts; `keyProb` is the probability of `KeyHit` before a collision,
  in the simulated world with the collision flag `collO`.
* `hO`, `KeyHitJ`: the simulated world with the indices of the client shares, and `KeyHit` at a
  session of the `j`-th share; `hOx`: the same world with the `j`-th share fixed.
* `RGood`: the event of the world of the reduction on which `extractT` outputs `g^{xy}`.
* `simO`, `simInit`, `fStepD`: the simulated world as distributions.
* `RW`, `redO`, `extractT`, `tlsGdhOut`, `tlsGdhRed`: the world of the reduction and the
  reduction.
* `tlsGdhBound`, `tlsCollBound`: the bounds.
* `Coupled`: a coupling of two distributions for a relation.
* `XIn`, `Cpl`: the external inputs of the sessions keyed by the functionality, and the coupling
  invariant between the filtered and the simulated world.

## Main results

* `filt_advantage_le_badGame`: the advantage between the filtered and the simulated game is at
  most the probability of the bad event.
* `absDiff_le_of_coupled`: oracles whose steps are coupled up to a bad transition give output
  probabilities within the probability of the flag.
* `step_coupled`: a step of the two worlds from coupled states reaches `KeyHit` or gives equal
  answers and coupled states.
* `badGame_le_gapDH`: that probability is at most `tlsGdhBound + tlsCollBound`, from
  `keyProb_le_gapDH` and `collProb_le`.
* `run_flagWhen_le_count`: a bad flag whose per-step probability grows by a bounded count.
* `keyProb_le_sum`, `keyHitJ_eager`, `keyHitJ_le_gapDH`: the union over the indices of the
  client shares, the eager draw of the `j`-th share, and the bound of each index by the advantage
  of the reduction, through `flag_le_final_of_coupled` and `red_coupling`.
* `tls_filt_realizesSim_gapDH`, `tls_realizesSim_gapDH`: the squares of the filtered and of the
  real protocol.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.TLSSquareGDH

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract (DHGroup)
open CatCrypt.Crypto.Signatures
open CatCrypt.Crypto.Assumptions
open CatCrypt.Crypto.AKE.X3DHSquare (KDFOp lazyKDF FEv FOut subView)
open CatCrypt.Crypto.AKE.TLSSquare
open CatCrypt.Crypto.AKE.TLSSquareSigned (tlsSigBound advantage_real_filt_le)
open CatCrypt.Crypto.AKE.X3DHSquareGDH (gapDHDef symEq)
open CatCrypt.Crypto.OracleGameUpToBad
open CatCrypt.Crypto.Messaging.SignalStackUC (fwdOut)
open scoped ENNReal

/-! ## Transcript injectivity -/

/-- **Injectivity of the transcript operations**: each operation determines its arguments. -/
def TrInj {Tr W VK Sig Sec : Type} (trs : TrOps Tr W VK Sig Sec) : Prop :=
  (∀ sid c s X Y sid' c' s' X' Y', trs.tr1 sid c s X Y = trs.tr1 sid' c' s' X' Y' →
      sid = sid' ∧ c = c' ∧ s = s' ∧ X = X' ∧ Y = Y') ∧
    (∀ t v t' v', trs.trCert t v = trs.trCert t' v' → t = t' ∧ v = v') ∧
    (∀ t σ t' σ', trs.trCV t σ = trs.trCV t' σ' → t = t' ∧ σ = σ') ∧
    (∀ t f t' f', trs.trSF t f = trs.trSF t' f' → t = t' ∧ f = f') ∧
    (∀ t f t' f', trs.trCF t f = trs.trCF t' f' → t = t' ∧ f = f')

/-! ## The bad event -/

section Bad

variable {S W Tr VK SK Sig Sec : Type}

/-- The input `i` is an external stage input of a session whose recorded input is `ip` (label
`cap` at the transcript `tSF` up to server Finished and the (EC)DHE value `Z`): `cap`, `sap` or
`exp` at `tSF`, or `res` at `tSF` extended by a client Finished, with the value `Z`. -/
def ExtIn (A : TLSAlg S W Tr VK SK Sig Sec) (ip i : TInp Tr W) : Prop :=
  i.dhe = ip.dhe ∧
    ((i.lbl = .cap ∨ i.lbl = .sap ∨ i.lbl = .exp) ∧ i.tr = ip.tr ∨
      i.lbl = .res ∧ ∃ cf, i.tr = A.trCF ip.tr cf)

/-- **A query at the key of a fresh session**: the key-derivation table of the simulator's copy
holds an external stage input of a session whose key the functionality chose. -/
def KeyHit (A : TLSAlg S W Tr VK SK Sig Sec)
    (t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) : Prop :=
  ∃ x r ip i k, t.2.recs x = some r ∧ r.status = .completed ∧ t.1.2.1 x = some ip ∧
    (i, k) ∈ t.1.1.ro ∧ ExtIn A ip i

/-- **A collision of a client share**: the step is a `hello` of the client session `(sid, c)`
that draws its share, and the share is the share that a server session `(sid, s)` naming `c` as
its peer already received. -/
def CollAt (A : TLSAlg S W Tr VK SK Sig Sec)
    (s : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) (e : TOEv W Tr Sig Sec)
    (x : TOOut W VK SK Sig Sec × (TSimSt S W Tr VK SK Sig Sec × St (TKey Sec))) : Prop :=
  ∃ sid c xs sv r Y vk σ sf Z cf, e = .inr (.hello sid c) ∧ s.1.1.eph (sid, c) = none ∧
    x.2.1.1.eph (sid, c) = some xs ∧ s.2.recs (sid, sv) = some r ∧ r.peer = c ∧
    s.1.1.srv (sid, sv) =
      some (A.trSF (A.trCV (A.trCert (A.tr1 sid c sv (A.pub xs) Y) vk) σ) sf, Z, cf)

/-- **The bad event of the simulated world**: after the step the table holds the key input of a
fresh session (`KeyHit`), or the step is a collision of a client share (`CollAt`). -/
def TBad (A : TLSAlg S W Tr VK SK Sig Sec)
    (s : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) (e : TOEv W Tr Sig Sec)
    (x : TOOut W VK SK Sig Sec × (TSimSt S W Tr VK SK Sig Sec × St (TKey Sec))) : Prop :=
  KeyHit A x.2 ∨ CollAt A s e x

end Bad

section BadProb

variable {S W Tr VK SK Sig Sec : Type} [Fintype S] [Nonempty S] [DecidableEq W]
  [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec] [Nonempty Sec] [Inhabited Sec]

/-- The oracle of the simulated game, at its state type. -/
noncomputable def simO (A : TLSAlg S W Tr VK SK Sig Sec)
    (t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) (e : TOEv W Tr Sig Sec) :
    PMF (TOOut W VK SK Sig Sec × (TSimSt S W Tr VK SK Sig Sec × St (TKey Sec))) :=
  (simGame A).oracle () t e

/-- The initial state of the simulated game, at its state type. -/
noncomputable def simInit (A : TLSAlg S W Tr VK SK Sig Sec) :
    TSimSt S W Tr VK SK Sig Sec × St (TKey Sec) :=
  (simGame A).init

open Classical in
/-- **The probability of the bad event**: the oracle adversary `B` runs against the simulated
world `simGame A`, and the flag records whether a step satisfied `TBad A`. -/
noncomputable def badProb (A : TLSAlg S W Tr VK SK Sig Sec)
    (B : OracleAdv (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) Bool) : ℝ≥0∞ :=
  (OracleAdv.run (OracleAdv.flagWhen (TBad A) (simO A)) B (simInit A, false)).toOuterMeasure
    {y | y.2.2 = true}

open Classical in
/-- The simulated world with the collision flag: the flag records whether a step satisfied
`CollAt A`. -/
noncomputable def collO (A : TLSAlg S W Tr VK SK Sig Sec) :
    (TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) × Bool → TOEv W Tr Sig Sec →
      PMF (TOOut W VK SK Sig Sec × ((TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) × Bool)) :=
  OracleAdv.flagWhen (CollAt A) (simO A)

open Classical in
/-- **The probability of a query at the key of a fresh session before a collision**: the
oracle adversary `B` runs against the simulated world with the collision flag, and the flag of
the run records whether a step reached `KeyHit A` while no collision of a client share had
occurred. -/
noncomputable def keyProb (A : TLSAlg S W Tr VK SK Sig Sec)
    (B : OracleAdv (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) Bool) : ℝ≥0∞ :=
  (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => KeyHit A x.2.1 ∧ x.2.2 = false) (collO A)) B
    ((simInit A, false), false)).toOuterMeasure {y | y.2.2 = true}

open Classical in
/-- The probability of a collision of a client share in the simulated world. -/
noncomputable def collProb (A : TLSAlg S W Tr VK SK Sig Sec)
    (B : OracleAdv (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) Bool) : ℝ≥0∞ :=
  (OracleAdv.run (OracleAdv.flagWhen (CollAt A) (simO A)) B (simInit A, false)).toOuterMeasure
    {y | y.2.2 = true}

open Classical in
/-- **The union bound of the two bad events**: a step of `TBad` is a collision, or reaches
`KeyHit` after a run without collision. -/
theorem badProb_le (A : TLSAlg S W Tr VK SK Sig Sec)
    (B : OracleAdv (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) Bool) :
    badProb A B ≤ keyProb A B + collProb A B := by
  let O₂ := OracleAdv.flagWhen
    (fun (_ : (TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) × Bool) (_ : TOEv W Tr Sig Sec)
      (x : TOOut W VK SK Sig Sec × ((TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) × Bool)) =>
      KeyHit A x.2.1 ∧ x.2.2 = false) (collO A)
  have h₁ : (OracleAdv.run O₂ B ((simInit A, false), false)).map (Prod.map id Prod.fst) =
      OracleAdv.run (collO A) B (simInit A, false) :=
    OracleAdv.run_flagWhen_map _ _ B _ false
  have h₃ : (OracleAdv.run O₂ B ((simInit A, false), false)).map
      (Prod.map id fun st => (st.1.1, st.1.2 || st.2)) =
        OracleAdv.run (OracleAdv.flagWhen (TBad A) (simO A)) B (simInit A, false) :=
    OracleAdv.run_map_state _ _ _ (fun st d => by
      simp only [O₂, collO, OracleAdv.flagWhen, PMF.map_comp]
      congr 1
      funext x
      simp only [Function.comp_apply, Prod.map_apply, id_eq, TBad]
      by_cases hk : KeyHit A x.2 <;> by_cases hc : CollAt A st.1.1 d x <;>
        cases st.1.2 <;> cases st.2 <;> simp [hk, hc]) B _
  unfold badProb keyProb collProb
  rw [← h₃, PMF.toOuterMeasure_map_apply]
  have h₄ : (OracleAdv.run (OracleAdv.flagWhen (CollAt A) (simO A)) B
      (simInit A, false)).toOuterMeasure {y | y.2.2 = true} =
      (OracleAdv.run O₂ B ((simInit A, false), false)).toOuterMeasure
        {y | y.2.1.2 = true} := by
    change (OracleAdv.run (collO A) B (simInit A, false)).toOuterMeasure _ = _
    rw [← h₁, PMF.toOuterMeasure_map_apply]
    rfl
  rw [h₄, add_comm]
  refine (MeasureTheory.measure_mono ?_).trans (MeasureTheory.measure_union_le _ _)
  intro y hy
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hy
  grind

end BadProb

/-! ## The simulated world as distributions -/

section SimP

/-- A step of the adversary port of `F_AKEImp … srvImp true` with the fresh key `kf`. -/
def fAdvD {K : Type} (t : St K) (a : AEv K) (kf : K) : St K × AOut :=
  match a with
  | .idle => (t, .ack)
  | .poll => ((pollStep t).1, .notice (pollStep t).2)
  | .corrupt pid => (corruptStep t pid, .ack)
  | .impersonate sid pid => (impStepOf srvImp t (sid, pid), .ack)
  | .newKey sid pid k => (newKeyStep t (sid, pid) k kf, .ack)
  | .newKeyUnlinked sid pid k => (newKeyFreshStep t (sid, pid) k kf, .ack)

/-- A step of `F_AKEImp … srvImp true` with the fresh key `kf`. -/
def fStepD {K : Type} (t : St K) (g : FEv K) (kf : K) : St K × FOut K :=
  match g with
  | .inl h => ((honStep t h).1, .inl (honStep t h).2)
  | .inr a => ((fAdvD t a kf).1, .inr (fAdvD t a kf).2)

/-- A step of `F_AKEImp … srvImp true` with uniform keys is the lift of the image of a uniform
key under `fStepD`. -/
theorem fImp_step_eq {K : Type} [Fintype K] [Nonempty K] (t : St K) (g : FEv K) :
    (F_AKEImp (SPComp.sample K) srvImp true).step t g =
      liftPMF ((PMF.uniformFintype K).map (fStepD t g)) := by
  change _ = liftPMF ((PMF.uniformFintype K).map fun kf => fStepD t g kf)
  rcases g with h | a
  · simp only [F_AKEImp, F_AKEImpK, Sys.ofPorts_step_inl, honSys, liftPMF_pure,
      map_liftPMF, PMF.pure_map]
    exact congrArg liftPMF (PMF.map_const _ _).symm
  · simp only [F_AKEImp, F_AKEImpK, Sys.ofPorts_step_inr, advSysImp]
    cases a <;>
      simp only [liftPMF_pure, sample_eq_liftPMF, map_liftPMF, PMF.pure_map, PMF.map_comp,
        ↓reduceIte] <;>
      first
      | exact congrArg liftPMF (PMF.map_const _ _).symm
      | rfl

variable {S W Tr VK SK Sig Sec : Type} [Fintype S] [Nonempty S] [DecidableEq W]
  [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec] [Nonempty Sec] [Inhabited Sec]
  (A : TLSAlg S W Tr VK SK Sig Sec)

/-- The start of the simulator as a distribution. -/
noncomputable def simStartP (s : TSimSt S W Tr VK SK Sig Sec) (e : TOEv W Tr Sig Sec) :
    PMF (TSimSt S W Tr VK SK Sig Sec × (FEv (TKey Sec) ⊕ TOOut W VK SK Sig Sec)) :=
  (simCore A s e).map fun q => (q.1, liftDec q.2)

/-- **The oracle of the simulated game** as a step of the simulator over the functionality, given
by distributions. -/
theorem simO_eq (t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) (e : TOEv W Tr Sig Sec) :
    simO A t e = (withSubP (simStartP A)
      (fun t g => (PMF.uniformFintype (TKey Sec)).map (fStepD t g))
      (fun s o => PMF.pure (simReset s, .inr (fwdOut .ack s.2.2 o)))
      (fun s o => PMF.pure (simReset s, fwdOut .ack s.2.2 o)) 0 t e).map Prod.swap := by
  have hstep := withSub_step_eq_liftPMF (tlsSimProt A)
    (F_AKEImp (SPComp.sample (TKey Sec)) srvImp true) (simStartP A)
    (fun t g => (PMF.uniformFintype (TKey Sec)).map (fStepD t g))
    (fun s o => PMF.pure (simReset s, .inr (fwdOut .ack s.2.2 o)))
    (fun s o => PMF.pure (simReset s, fwdOut .ack s.2.2 o))
    (fun s e => by simp only [tlsSimProt, simStart, simStartP]; rw [map_liftPMF])
    fImp_step_eq (fun _ _ => liftPMF_pure _) (fun _ _ => liftPMF_pure _) t e
  change (simWorld_pureNF A t e).pmf.map Prod.swap = _
  rw [X3DHSquareHops.pmf_eq_of_eq_liftPMF (simWorld_pureNF A t e) hstep]
  rfl

/-- **`hello` in the simulated world** is `helloStep` on the copy, without a call of the
functionality. -/
theorem simO_hello (t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) (sid : SessionId)
    (c : PartyId) :
    simO A t (.inr (.hello sid c)) = (helloStep A t.1.1 (sid, c)).map fun p =>
      (.inr p.1, ((p.2, t.1.2.1, none), t.2)) := by
  rw [simO_eq]
  simp only [withSubP, simStartP, simCore, realAdvK, PMF.map_comp, PMF.bind_map, PMF.map_bind]
  rw [← PMF.bind_pure_comp]
  congr 1
  funext a
  simp only [Function.comp_apply, liftDec, driveP, PMF.pure_map]
  rfl

/-- After a step of the simulated world the functionality is unchanged or made a step. -/
theorem simO_f (t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) (e : TOEv W Tr Sig Sec)
    (x : TOOut W VK SK Sig Sec × (TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)))
    (hx : x ∈ (simO A t e).support) :
    x.2.2 = t.2 ∨ ∃ g kf, x.2.2 = (fStepD t.2 g kf).1 := by
  rw [simO_eq] at hx
  simp only [withSubP, PMF.support_map, PMF.support_bind, Set.mem_image, Set.mem_iUnion] at hx
  obtain ⟨_, ⟨⟨s, g | o⟩, -, y, hy, rfl⟩, rfl⟩ := hx
  · simp only [driveP, PMF.support_bind, PMF.support_map, PMF.support_pure, Set.mem_iUnion,
      Set.mem_image, Set.mem_singleton_iff, PMF.support_uniformFintype] at hy
    grind
  · simp only [driveP, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact Or.inl rfl

end SimP

/-! ## The collision of a client share -/

section Coll

/-- **A bad flag with a growing per-step bound.** Let an invariant `I` hold along the steps, let
every step increase `Ψ` by at most one, and let a step from `s` make a bad transition with
probability at most `Ψ s * ε`. An adversary with at most `n` queries started at `s` with
`Ψ s + n ≤ M` sets the flag with probability at most `n * (M * ε)`. -/
theorem run_flagWhen_le_count {σ D R α : Type} (O : σ → D → PMF (R × σ))
    (bad : σ → D → R × σ → Prop) [∀ s d x, Decidable (bad s d x)] (I : σ → Prop) (Ψ : σ → ℕ)
    (ε : ℝ≥0∞) (hI : ∀ s d, I s → ∀ x ∈ (O s d).support, I x.2 ∧ Ψ x.2 ≤ Ψ s + 1)
    (hbad : ∀ s d, I s → (O s d).toOuterMeasure {x | bad s d x} ≤ Ψ s * ε)
    (A : OracleAdv D R α) (n M : ℕ) (hA : A.IsQueryBound n) (s : σ) (hs : I s)
    (hM : Ψ s + n ≤ M) :
    (OracleAdv.run (OracleAdv.flagWhen bad O) A (s, false)).toOuterMeasure
      {y | y.2.2 = true} ≤ n * (M * ε) := by
  refine (OracleAdv.run_flagWhen_le_sum_of_inv O bad I Ψ 1 (fun L => (L : ℝ≥0∞) * ε)
    (fun _ _ h => by dsimp only; gcongr) hI hbad A n hA s hs).trans ?_
  calc _ ≤ ∑ _i ∈ Finset.range n, (M : ℝ≥0∞) * ε := Finset.sum_le_sum fun i hi => by
        have := Finset.mem_range.mp hi
        gcongr
        exact_mod_cast (by omega : Ψ s + i * 1 ≤ M)
    _ = n * (M * ε) := by simp

/-- A set with at most one element has uniform probability at most `1 / |S|`. -/
theorem uniform_le_of_subsingleton {S : Type} [Fintype S] [Nonempty S] (T : Set S)
    (h : T.Subsingleton) :
    (PMF.uniformFintype S).toOuterMeasure T ≤ (Fintype.card S : ℝ≥0∞)⁻¹ := by
  rcases h.eq_empty_or_singleton with rfl | ⟨a, rfl⟩
  · simp
  · rw [PMF.toOuterMeasure_apply_singleton]
    simp [PMF.uniformFintype]

/-- A union of subsingletons indexed by a list has uniform probability at most its length over
`|S|`. -/
theorem uniform_list_le {S α : Type} [Fintype S] [Nonempty S] (T : α → Set S)
    (h : ∀ a, (T a).Subsingleton) (L : List α) :
    (PMF.uniformFintype S).toOuterMeasure {x | ∃ a ∈ L, x ∈ T a} ≤
      L.length * (Fintype.card S : ℝ≥0∞)⁻¹ := by
  induction L with
  | nil => simp
  | cons b L ih =>
    have hsub : {x | ∃ a ∈ b :: L, x ∈ T a} ⊆ T b ∪ {x | ∃ a ∈ L, x ∈ T a} := by
      rintro x ⟨a, ha, hx⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · exact Or.inl hx
      · exact Or.inr ⟨a, ha, hx⟩
    refine (MeasureTheory.measure_mono hsub).trans
      ((MeasureTheory.measure_union_le _ _).trans ?_)
    calc _ ≤ (Fintype.card S : ℝ≥0∞)⁻¹ + L.length * (Fintype.card S : ℝ≥0∞)⁻¹ :=
          add_le_add (uniform_le_of_subsingleton _ (h b)) ih
      _ = _ := by simp only [List.length_cons]; push_cast; ring

/-- Every record of the functionality has a notice. -/
def RecNoticed {K : Type} (f : St K) : Prop :=
  ∀ y, (f.recs y).isSome → ∃ n ∈ f.notices, n.sid = y.1 ∧ n.pid = y.2

/-- A step of the functionality adds at most one notice and keeps every record noticed. -/
theorem fStepD_frame {K : Type} (f : St K) (g : FEv K) (kf : K) (hf : RecNoticed f) :
    (fStepD f g kf).1.notices.length ≤ f.notices.length + 1 ∧ RecNoticed (fStepD f g kf).1 := by
  have hsame : ∀ f' : St K, f'.notices = f.notices →
      (∀ y, (f'.recs y).isSome → (f.recs y).isSome) →
      f'.notices.length ≤ f.notices.length + 1 ∧ RecNoticed f' := fun f' hn hr =>
    ⟨by rw [hn]; omega, fun y hy => by rw [hn]; exact hf y (hr y hy)⟩
  have hset : ∀ (x : Inst) (r : Rec K), (f.recs x).isSome →
      ∀ y, ((setRec f x r).recs y).isSome → (f.recs y).isSome := fun x r hx y hy => by
    by_cases hyx : y = x
    · subst hyx; exact hx
    · simpa [setRec, Function.update_of_ne hyx] using hy
  rcases g with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) |
    (_ | _ | pid | ⟨sid, pid⟩ | ⟨sid, pid, k⟩ | ⟨sid, pid, k⟩)
  · simp only [fStepD, honStep, addSession]
    split
    · exact hsame _ rfl fun _ h => h
    · refine ⟨by simp, fun y hy => ?_⟩
      by_cases hyx : y = (sid, pid)
      · subst hyx
        exact ⟨⟨sid, pid, peer, role⟩, by simp, rfl, rfl⟩
      · simp only [Function.update_of_ne hyx] at hy
        obtain ⟨n, hn, h⟩ := hf y hy
        exact ⟨n, List.mem_append_left _ hn, h⟩
  · exact hsame _ rfl fun _ h => h
  · exact hsame _ rfl fun _ h => h
  · simp only [fStepD, fAdvD, pollStep]
    split <;> exact hsame _ rfl fun _ h => h
  · exact hsame _ rfl fun _ h => h
  · simp only [fStepD, fAdvD, impStepOf, impStep]
    split
    · rename_i r hr
      simp only
      split_ifs
      · exact hsame _ rfl (hset _ _ (by simp [hr]))
      all_goals exact hsame _ rfl fun _ h => h
    · exact hsame _ rfl fun _ h => h
  · simp only [fStepD, fAdvD, newKeyStep]
    split
    · rename_i r hr
      split
      · exact hsame _ rfl (hset _ _ (by simp [hr]))
      · exact hsame _ rfl fun _ h => h
    · exact hsame _ rfl fun _ h => h
  · simp only [fStepD, fAdvD, newKeyFreshStep]
    split
    · rename_i r hr
      split
      · exact hsame _ rfl (hset _ _ (by simp [hr]))
      · exact hsame _ rfl fun _ h => h
    · exact hsame _ rfl fun _ h => h

/-- The client secrets of the session `(sid, c)` whose share a server session of the notice `n`
in `sid`, naming `c`, already received. -/
def collSet {S W Tr VK SK Sig Sec : Type} [Field S] (G : DHGroup S W)
    (trs : TrOps Tr W VK Sig Sec) (t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec))
    (sid : SessionId) (c : PartyId) (n : Notice) : Set S :=
  {xs | ∃ r Y vk σ sf Z cf, n.sid = sid ∧ t.2.recs (sid, n.pid) = some r ∧ r.peer = c ∧
    t.1.1.srv (sid, n.pid) = some (trs.trSF (trs.trCV (trs.trCert
      (trs.tr1 sid c n.pid (G.pub xs) Y) vk) σ) sf, Z, cf)}

/-- With injective transcript operations a server session received at most one share. -/
theorem collSet_subsingleton {S W Tr VK SK Sig Sec : Type} [Field S] (G : DHGroup S W)
    (trs : TrOps Tr W VK Sig Sec) (hT : TrInj trs)
    (t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) (sid : SessionId) (c : PartyId)
    (n : Notice) : (collSet G trs t sid c n).Subsingleton := by
  rintro a ⟨r, Y, vk, σ, sf, Z, cf, -, -, -, ha⟩ b ⟨r', Y', vk', σ', sf', Z', cf', -, -, -, hb⟩
  rw [ha, Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨h1, -⟩ := hT.2.2.2.1 _ _ _ _ hb.1
  obtain ⟨h1, -⟩ := hT.2.2.1 _ _ _ _ h1
  obtain ⟨h1, -⟩ := hT.2.1 _ _ _ _ h1
  obtain ⟨-, -, -, h1, -⟩ := hT.1 _ _ _ _ _ _ _ _ _ _ h1
  exact G.pub.injective h1

variable {S W Tr VK SK Sig Sec : Type} [Field S] [Fintype S] [SampleableType W]
  [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec] [Nonempty Sec] [Inhabited Sec]
  (G : DHGroup S W) (Sg : PSigScheme Tr VK SK Sig) (trs : TrOps Tr W VK Sig Sec)

/-- **A step of the simulated world is a collision with probability at most the number of
notices over `|S|`.** -/
theorem collAt_step_le (hT : TrInj trs) (t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec))
    (d : TOEv W Tr Sig Sec) (ht : RecNoticed t.2) :
    (simO (tlsDHAlg G Sg trs) t d).toOuterMeasure {x | CollAt (tlsDHAlg G Sg trs) t d x} ≤
      t.2.notices.length * (Fintype.card S : ℝ≥0∞)⁻¹ := by
  by_cases hd : ∃ sid c, d = .inr (.hello sid c) ∧ t.1.1.eph (sid, c) = none
  · obtain ⟨sid, c, rfl, he⟩ := hd
    have hsub : {x | CollAt (tlsDHAlg G Sg trs) t (.inr (.hello sid c)) x} ⊆
        {x | ∃ xs, x.2.1.1.eph (sid, c) = some xs ∧
          ∃ n ∈ t.2.notices, xs ∈ collSet G trs t sid c n} := by
      rintro x ⟨sid', c', xs, sv, r, Y, vk, σ, sf, Z, cf, hd, -, hx, hr, hp, hs⟩
      simp only [Sum.inr.injEq, TEv.hello.injEq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      obtain ⟨n, hn, hn1, hn2⟩ := ht (sid, sv) (by simp [hr])
      refine ⟨xs, hx, n, hn, r, Y, vk, σ, sf, Z, cf, hn1, ?_⟩
      have hsv : n.pid = sv := hn2
      subst hsv
      exact ⟨hr, hp, hs⟩
    refine (MeasureTheory.measure_mono hsub).trans ?_
    rw [simO_hello, PMF.toOuterMeasure_map_apply]
    have hpure : ∀ o : TOut W VK SK Sig Sec,
        (PMF.pure (o, t.1.1)).toOuterMeasure
          ((fun p => ((Sum.inr p.1 : TOOut W VK SK Sig Sec), (p.2, t.1.2.1,
            (none : Option (TOut W VK SK Sig Sec))), t.2)) ⁻¹'
          {x | ∃ xs, x.2.1.1.eph (sid, c) = some xs ∧
            ∃ n ∈ t.2.notices, xs ∈ collSet G trs t sid c n}) ≤
          t.2.notices.length * (Fintype.card S : ℝ≥0∞)⁻¹ := fun o => by
      simp [PMF.toOuterMeasure_pure_apply, he]
    unfold helloStep
    split
    · split_ifs
      · split
        · rename_i xs0 hx0
          rw [he] at hx0
          cases hx0
        · rw [PMF.toOuterMeasure_map_apply]
          refine (MeasureTheory.measure_mono ?_).trans (uniform_list_le
            (collSet G trs t sid c) (collSet_subsingleton G trs hT t sid c) t.2.notices)
          rintro xs ⟨xs', hx', hn⟩
          simp only [Function.update_self, Option.some.injEq] at hx'
          subst hx'
          exact hn
      · exact hpure _
    · exact hpure _
  · refine le_of_eq_of_le ?_ zero_le
    refine MeasureTheory.measure_mono_null (fun x hx => ?_) MeasureTheory.measure_empty
    obtain ⟨sid, c, xs, sv, r, Y, vk, σ, sf, Z, cf, rfl, he, -⟩ := hx
    exact hd ⟨sid, c, rfl, he⟩

end Coll

/-! ## The indices of the client shares -/

section Index

open Classical in
/-- **A bad flag implied by another below a query budget.** Let every call keep an invariant `I`
and increase the count `q` by at most one, and let `P` imply `Q` at the states of `I` whose count
is at most `n`, for `n ≥ 1`. An adversary with at most `m` queries started at `s` with
`q s + m ≤ n` sets the flag of `P` with at most the probability of the flag of `Q`. -/
theorem run_flag_le_of_budget {σ D R α : Type} (O : σ → D → PMF (R × σ)) (P Q : σ → Prop)
    (I : σ → Prop) (q : σ → ℕ) (n : ℕ)
    (hI : ∀ s d, I s → ∀ x ∈ (O s d).support, I x.2 ∧ q x.2 ≤ q s + 1)
    (hPQ : ∀ s, I s → q s ≤ n → 1 ≤ n → P s → Q s)
    (A : OracleAdv D R α) (m : ℕ) (hA : A.IsQueryBound m) (s : σ) (hs : I s)
    (hm : q s + m ≤ n) :
    (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => P x.2) O) A (s, false)).toOuterMeasure
        {y | y.2.2 = true} ≤
      (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => Q x.2) O) A (s, false)).toOuterMeasure
        {y | y.2.2 = true} := by
  induction A generalizing s m with
  | ret a =>
    rw [OracleAdv.run_ret, PMF.toOuterMeasure_pure_apply]
    simp
  | rand p k ih =>
    rw [OracleAdv.run_rand, OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply,
      PMF.toOuterMeasure_bind_apply]
    exact ENNReal.tsum_le_tsum fun c => mul_le_mul_right (ih c m (hA c) s hs hm) _
  | query d k ih =>
    cases m with
    | zero => exact hA.elim
    | succ m =>
    rw [OracleAdv.run_query, OracleAdv.run_query]
    simp only [OracleAdv.flagWhen, PMF.bind_map, PMF.toOuterMeasure_bind_apply]
    refine ENNReal.tsum_le_tsum fun x => ?_
    by_cases hx : x ∈ (O s d).support
    · refine mul_le_mul_right ?_ _
      simp only [Function.comp_apply, Bool.false_or]
      obtain ⟨hIx, hqx⟩ := hI s d hs x hx
      by_cases h₁ : P x.2
      · rw [decide_eq_true h₁, decide_eq_true (hPQ _ hIx (by omega) (by omega) h₁),
          X3DHSquareGDH.run_flag_true_one, X3DHSquareGDH.run_flag_true_one]
      · rw [decide_eq_false h₁]
        by_cases h₂ : Q x.2
        · rw [decide_eq_true h₂, X3DHSquareGDH.run_flag_true_one]
          exact X3DHSquareGDH.toOuterMeasure_le_one _ _
        · rw [decide_eq_false h₂]
          exact ih x.1 m (hA x.1) x.2 hIx (by omega)
    · rw [(PMF.apply_eq_zero_iff _ _).mpr hx, zero_mul, zero_mul]

variable {S W Tr VK SK Sig Sec : Type} [Fintype S] [Nonempty S] [DecidableEq W]
  [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec] [Nonempty Sec] [Inhabited Sec]
  (A : TLSAlg S W Tr VK SK Sig Sec)

/-- The state of the simulated world with the collision flag, the number of client shares drawn
and the index of the draw of each client session. -/
abbrev HSt (S W Tr VK SK Sig Sec : Type) :=
  ((TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) × Bool) × ℕ × (Inst → Option ℕ)

/-- The client session whose share the step at `e` from `t` to `t'` draws, if any. -/
def drawAt (t t' : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) :
    TOEv W Tr Sig Sec → Option Inst
  | .inr (.hello sid pid) =>
    if (t.1.1.eph (sid, pid)).isNone && (t'.1.1.eph (sid, pid)).isSome then some (sid, pid)
    else none
  | _ => none

/-- The number of client shares drawn and the indices of the draws after the step at `e` from
`t` to `t'`: a draw receives the current number as its index. -/
def idxStep (t t' : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) (e : TOEv W Tr Sig Sec)
    (c : ℕ × (Inst → Option ℕ)) : ℕ × (Inst → Option ℕ) :=
  match drawAt t t' e with
  | some z => (c.1 + 1, Function.update c.2 z (some c.1))
  | none => c

/-- **The simulated world with the collision flag and the indices of the client shares.** -/
noncomputable def hO (a : HSt S W Tr VK SK Sig Sec) (e : TOEv W Tr Sig Sec) :
    PMF (TOOut W VK SK Sig Sec × HSt S W Tr VK SK Sig Sec) :=
  (collO A a.1 e).map fun y => (y.1, (y.2, idxStep a.1.1 y.2.1 e a.2))

/-- The initial state of `hO`. -/
noncomputable def hInit : HSt S W Tr VK SK Sig Sec := ((simInit A, false), 0, fun _ => none)

/-- The client session of the protocol session of `z` with the record `r`: `z` for an initiator,
the session of its peer for a responder. -/
def clientOf {K : Type} (z : Inst) (r : Rec K) : Inst :=
  (z.1, if r.role = .initiator then z.2 else r.peer)

/-- **A query at the key of a fresh session of the `j`-th client share** before a collision: the
table holds an external stage input of a session whose key the functionality chose and whose
client session drew the `j`-th share (or, for `j = 0`, drew no share). -/
def KeyHitJ (j : ℕ) (a : HSt S W Tr VK SK Sig Sec) : Prop :=
  a.1.2 = false ∧ ∃ z r ip i k, a.1.1.2.recs z = some r ∧ r.status = .completed ∧
    a.1.1.1.2.1 z = some ip ∧ (i, k) ∈ a.1.1.1.1.ro ∧ ExtIn A ip i ∧
    (a.2.2 (clientOf z r) = some j ∨ (a.2.2 (clientOf z r) = none ∧ j = 0))

open Classical in
/-- `keyProb` as the flag of `hO`. -/
theorem keyProb_eq_hO (B : OracleAdv (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) Bool) :
    keyProb A B = (OracleAdv.run (OracleAdv.flagWhen
      (fun _ _ y => KeyHit A y.2.1.1 ∧ y.2.1.2 = false) (hO A)) B
        (hInit A, false)).toOuterMeasure {y | y.2.2 = true} := by
  have h := OracleAdv.run_map_state
    (OracleAdv.flagWhen (fun _ _ y => KeyHit A y.2.1.1 ∧ y.2.1.2 = false) (hO A))
    (OracleAdv.flagWhen (fun _ _ x => KeyHit A x.2.1 ∧ x.2.2 = false) (collO A))
    (fun u => (u.1.1, u.2)) (fun u d => by
      simp only [hO, OracleAdv.flagWhen, PMF.map_comp]
      rfl) B (hInit A, false)
  have h0 : ((hInit A, false).1.1, (hInit A, false).2) = ((simInit A, false), false) := rfl
  rw [h0] at h
  unfold keyProb
  rw [← h, PMF.toOuterMeasure_map_apply]
  rfl

open Classical in
/-- **The union over the indices of the client shares**: before a collision, `KeyHit` is
`KeyHitJ j` for an index `j < n` of an adversary with at most `n` queries. -/
theorem keyProb_le_sum (n : ℕ)
    (B : OracleAdv (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) Bool) (hB : B.IsQueryBound n) :
    keyProb A B ≤ ∑ j ∈ Finset.range n, (OracleAdv.run (OracleAdv.flagWhen
      (fun _ _ y => KeyHitJ A j y.2) (hO A)) B (hInit A, false)).toOuterMeasure
        {y | y.2.2 = true} := by
  have hb := run_flag_le_of_budget (hO A) (fun a => KeyHit A a.1.1 ∧ a.1.2 = false)
    (fun a => ∃ j ∈ Finset.range n, KeyHitJ A j a)
    (fun a => ∀ z m, a.2.2 z = some m → m < a.2.1) (fun a => a.2.1) n ?_ ?_ B n hB (hInit A)
    (fun _ _ h => by simp [hInit] at h) (by simp [hInit])
  · have hu := X3DHSquareGDH.run_flag_union_le (hO A) (KeyHitJ A) (Finset.range n) B (hInit A)
    rw [keyProb_eq_hO]
    refine le_trans ?_ hu
    convert hb using 6
  · intro a d ha y hy
    simp only [hO, PMF.support_map, Set.mem_image] at hy
    obtain ⟨w, -, rfl⟩ := hy
    simp only [idxStep]
    split
    · refine ⟨fun z m hz => ?_, by omega⟩
      grind
    · exact ⟨ha, by omega⟩
  · rintro a ha hn h1 ⟨hk, hc⟩
    obtain ⟨z, r, ip, i, k, h₁, h₂, h₃, h₄, h₅⟩ := hk
    rcases hz : a.2.2 (clientOf z r) with _ | m
    · exact ⟨0, Finset.mem_range.mpr h1, hc, z, r, ip, i, k, h₁, h₂, h₃, h₄, h₅,
        Or.inr ⟨hz, rfl⟩⟩
    · exact ⟨m, Finset.mem_range.mpr (by have := ha _ _ hz; omega), hc, z, r, ip, i, k, h₁, h₂,
        h₃, h₄, h₅, Or.inl hz⟩

/-- The `hello` of the client session `(sid, pid)` draws the `j`-th share: `j` shares are drawn
and the session is an initiator without share. -/
def HUse (j : ℕ) (a : HSt S W Tr VK SK Sig Sec) (sid : SessionId) (pid : PartyId) : Prop :=
  a.2.1 = j ∧ ∃ r, a.1.1.1.1.st.recs (sid, pid) = some r ∧ r.role = .initiator ∧
    a.1.1.1.1.eph (sid, pid) = none

open Classical in
/-- The answer and the state of `hO` after the `hello` of `(sid, pid)` that draws the secret
`xs`. -/
noncomputable def helloRes (a : HSt S W Tr VK SK Sig Sec) (sid : SessionId) (pid : PartyId)
    (xs : S) : TOOut W VK SK Sig Sec × HSt S W Tr VK SK Sig Sec :=
  let y : TOOut W VK SK Sig Sec × (TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) :=
    (.inr (.share (some (A.pub xs))),
      (({ a.1.1.1.1 with eph := Function.update a.1.1.1.1.eph (sid, pid) (some xs) },
        a.1.1.1.2.1, none), a.1.1.2))
  (y.1, ((y.2, a.1.2 || decide (CollAt A a.1.1 (.inr (.hello sid pid)) y)),
    idxStep a.1.1 y.2 (.inr (.hello sid pid)) a.2))

open Classical in
/-- **The simulated world with the `j`-th client share fixed** to the share of `x`: the `hello`
that draws the `j`-th share takes the secret `x`. -/
noncomputable def hOx (j : ℕ) (x : S) (a : HSt S W Tr VK SK Sig Sec) :
    TOEv W Tr Sig Sec → PMF (TOOut W VK SK Sig Sec × HSt S W Tr VK SK Sig Sec)
  | .inr (.hello sid pid) =>
    if HUse j a sid pid then PMF.pure (helloRes A a sid pid x) else hO A a (.inr (.hello sid pid))
  | e => hO A a e

/-- The `hello` that draws the `j`-th share in `hO` is the image of a uniform secret. -/
theorem hO_hello_use {j : ℕ} {a : HSt S W Tr VK SK Sig Sec} {sid : SessionId} {pid : PartyId}
    (h : HUse j a sid pid) :
    hO A a (.inr (.hello sid pid)) = (PMF.uniformFintype S).map (helloRes A a sid pid) := by
  obtain ⟨-, r, hr, hi, he⟩ := h
  simp only [hO, collO, OracleAdv.flagWhen, simO_hello, PMF.map_comp]
  unfold helloStep
  simp only [hr, hi, ↓reduceIte, he, PMF.map_comp]
  rfl

open Classical in
/-- **Eager sampling of the `j`-th client share**: the flag of `KeyHitJ j` in `hO` is the
average over `x` of its flag in `hOx j x`. -/
theorem keyHitJ_eager (j : ℕ)
    (B : OracleAdv (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) Bool) :
    (OracleAdv.run (OracleAdv.flagWhen (fun _ _ y => KeyHitJ A j y.2) (hO A)) B
        (hInit A, false)).toOuterMeasure {y | y.2.2 = true} =
      ∑' x, PMF.uniformFintype S x * (OracleAdv.run (OracleAdv.flagWhen
        (fun _ _ y => KeyHitJ A j y.2) (hOx A j x)) B (hInit A, false)).toOuterMeasure
          {y | y.2.2 = true} := by
  have hcnt : ∀ (a : HSt S W Tr VK SK Sig Sec) d y, a.2.1 ≤ (idxStep a.1.1 y d a.2).1 := by
    intro a d y
    unfold idxStep
    split <;> simp
  let use : HSt S W Tr VK SK Sig Sec → TOEv W Tr Sig Sec → Prop :=
    fun a d => ∃ sid pid, d = .inr (.hello sid pid) ∧ HUse j a sid pid
  have hno : ∀ x a d, ¬ use a d → hOx A j x a d = hO A a d := by
    intro x a d hd
    unfold hOx
    split
    · split_ifs with h
      · exact absurd ⟨_, _, rfl, h⟩ hd
      · rfl
    · rfl
  have huse : ∀ a d, use a d → hO A a d = (PMF.uniformFintype S).bind fun x => hOx A j x a d := by
    rintro a d ⟨sid, pid, rfl, hu⟩
    simp only [hOx, hu, ↓reduceIte, hO_hello_use A hu]
    exact (PMF.bind_pure_comp _ _).symm
  have hnext : ∀ x a d, use a d → ∀ y ∈ (hOx A j x a d).support, j < y.2.2.1 := by
    rintro x a d ⟨sid, pid, rfl, hu⟩ y hy
    simp only [hOx, hu, ↓reduceIte, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    obtain ⟨hj, r, -, -, he⟩ := hu
    simp only [helloRes, idxStep, drawAt, he, Option.isNone_none, Function.update_self,
      Option.isSome_some, Bool.and_self, ↓reduceIte]
    omega
  have hmono : ∀ a d, ∀ y ∈ (hO A a d).support, a.2.1 ≤ y.2.2.1 := by
    intro a d y hy
    simp only [hO, PMF.support_map, Set.mem_image] at hy
    obtain ⟨w, -, rfl⟩ := hy
    exact hcnt a d w.2.1
  have hnu : ∀ a d, j < a.2.1 → ¬ use a d := by
    rintro a d ha ⟨sid, pid, rfl, hu⟩
    have := hu.1
    omega
  rw [OracleAdv.run_eq_bind_run_of_trigger (PMF.uniformFintype S)
    (OracleAdv.flagWhen (fun _ _ y => KeyHitJ A j y.2) (hO A))
    (fun x => OracleAdv.flagWhen (fun _ _ y => KeyHitJ A j y.2) (hOx A j x))
    (fun t => t.1.2.1 ≤ j) (fun t d => use t.1 d) (fun _ t => j < t.1.2.1) ?_ ?_ ?_ ?_ ?_ ?_ B
    (hInit A, false) (by simp [hInit]), PMF.toOuterMeasure_bind_apply]
  · intro t d _ hu
    simp only [OracleAdv.flagWhen, huse t.1 d hu, PMF.map_bind]
  · intro x t d _ hu
    simp only [OracleAdv.flagWhen, hno x t.1 d hu]
  · intro t d _ _ y _
    exact (le_or_gt y.2.1.2.1 j).imp id fun h _ => h
  · intro x t d _ hu y hy
    simp only [OracleAdv.flagWhen, PMF.support_map, Set.mem_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact hnext x t.1 d hu z hz
  · intro x t d ht y hy
    simp only [OracleAdv.flagWhen, PMF.support_map, Set.mem_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact lt_of_lt_of_le ht (hmono t.1 d z hz)
  · intro x t d ht
    simp only [OracleAdv.flagWhen, hno x t.1 d (hnu t.1 d ht)]

end Index

/-! ## The world of the reduction -/

section Red

variable {S W Tr VK SK Sig Sec : Type} [Field S] [Fintype S] [SampleableType W]
  [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec] [Nonempty Sec] [Inhabited Sec]

/-- The state of the world of the reduction: the copy of the filtered state with symbolic
(EC)DHE values (a client secret `none` is the secret of the challenge share), the recorded input of
each completed session, the state of the functionality, the number of client shares drawn, and
the rerandomisation exponents of the server shares that received the challenge share. -/
structure RW (S W Tr VK SK Sec : Type) where
  /-- The copy, with symbolic (EC)DHE values and the symbolic table. -/
  c : TRStT (Option S) (W ⊕ W) Tr VK SK Sec (List (TInp Tr (W ⊕ W) × Sec))
  /-- The recorded input of each completed session. -/
  inp : Inst → Option (TInp Tr (W ⊕ W))
  /-- The state of the functionality. -/
  f : St (TKey Sec)
  /-- The number of client shares drawn. -/
  hellos : ℕ
  /-- The rerandomisation exponents. -/
  vs : List S

variable (G : DHGroup S W) (Sg : PSigScheme Tr VK SK Sig) (trs : TrOps Tr W VK Sig Sec)
  (i : ℕ) (O : W → W → W → Bool) (X Y : W)

/-- The equality of two symbolic inputs, decided with `O` at the challenge share `X`. -/
def sinpEq (j j' : TInp Tr (W ⊕ W)) : Bool :=
  decide (j.lbl = j'.lbl) && decide (j.tr = j'.tr) && symEq G O X j.dhe j'.dhe

/-- The lookup of a symbolic input in the symbolic table. -/
def slook (j : TInp Tr (W ⊕ W)) (tb : List (TInp Tr (W ⊕ W) × Sec)) : Option Sec :=
  (tb.find? fun p => sinpEq G O X j p.1).map Prod.snd

/-- The lazily sampled key derivation on the symbolic table. -/
noncomputable def sro (tb : List (TInp Tr (W ⊕ W) × Sec)) (j : TInp Tr (W ⊕ W)) :
    PMF (Sec × List (TInp Tr (W ⊕ W) × Sec)) :=
  match slook G O X j tb with
  | some v => PMF.pure (v, tb)
  | none => (PMF.uniformFintype Sec).map fun v => (v, (j, v) :: tb)

/-- The signing key pair of `pid` in the world of the reduction, drawn at its first use. -/
noncomputable def rlt (s : RW S W Tr VK SK Sec) (pid : PartyId) :
    PMF ((VK × SK) × RW S W Tr VK SK Sec) :=
  match s.c.lt pid with
  | some l => PMF.pure (l, s)
  | none => Sg.keyDist.map fun l =>
      (l, { s with c := { s.c with lt := Function.update s.c.lt pid (some l) } })

/-- The share of the client session `x`: the challenge share for a secret `none`. -/
def shareR (s : RW S W Tr VK SK Sec) (x : Inst) : Option W :=
  (s.c.eph x).map fun o => match o with
    | some xs => G.pub xs
    | none => X

/-- The key of the session `x` at the transcript `tSF`, the symbolic value `Z` and the client
Finished `cf`, on the symbolic table. -/
noncomputable def skeys (tb : List (TInp Tr (W ⊕ W) × Sec)) (tSF : Tr) (Z : W ⊕ W) (cf : Sec) :
    PMF (TKey Sec × List (TInp Tr (W ⊕ W) × Sec)) :=
  (sro G O X tb ⟨.cap, tSF, Z⟩).bind fun a => (sro G O X a.2 ⟨.sap, tSF, Z⟩).bind fun b =>
    (sro G O X b.2 ⟨.exp, tSF, Z⟩).bind fun c =>
      (sro G O X c.2 ⟨.res, trs.trCF tSF cf, Z⟩).map fun d => ((a.1, b.1, c.1, d.1), d.2)

/-- The completion of the session `x` in the world of the reduction, as `deliver` and the answer
of the functionality: an exposed session receives its key of the symbolic table, passed to
`newKey`; any other session receives the key of the functionality, `newKey` when its partner has
not completed or completed on the same input and `newKeyUnlinked` otherwise. -/
noncomputable def deliverR (s : RW S W Tr VK SK Sec) (x : Inst) (tSF : Tr) (Z : W ⊕ W)
    (cf : Sec) (o : TOut W VK SK Sig Sec) : PMF (TOOut W VK SK Sig Sec × RW S W Tr VK SK Sec) :=
  match s.c.st.recs x with
  | some r =>
    if Exposed s.c.st x r then
      (skeys G trs O X s.c.ro tSF Z cf).bind fun k =>
        (PMF.uniformFintype (TKey Sec)).map fun kf =>
          (.inr o, { s with c := setKey s.c x k.1 k.2,
                            inp := Function.update s.inp x (some ⟨.cap, tSF, Z⟩),
                            f := newKeyStep s.f x k.1 kf })
    else
      (PMF.uniformFintype (TKey Sec)).map fun kf =>
        (.inr o, { s with c := setKey s.c x default s.c.ro,
                          inp := Function.update s.inp x (some ⟨.cap, tSF, Z⟩),
                          f := if (s.inp (x.1, r.peer)).all (sinpEq G O X · ⟨.cap, tSF, Z⟩)
                            then newKeyStep s.f x default kf
                            else newKeyFreshStep s.f x default kf })
  | none => PMF.pure (.inr o, s)

/-- `srvRecv` at the server session `x` on the share `X'` in the world of the reduction: the
share `Y · g^v` for a drawn `v` when `X'` is the challenge share, `g^y` for a drawn `y`
otherwise; the server flight as in `srvRecvK`, preceded by `impersonate` when `X'` is not the
share of the client session named by the record. -/
noncomputable def srvRecvR (s : RW S W Tr VK SK Sec) (x : Inst) (X' : W) :
    PMF (TOOut W VK SK Sig Sec × RW S W Tr VK SK Sec) :=
  match s.c.st.recs x with
  | some r =>
    if r.role = .responder ∧ r.key.isNone ∧ (s.c.srv x).isNone then
      (rlt Sg s x.2).bind fun l => (PMF.uniformFintype S).bind fun v =>
        let Ys : W := if X' = X then G.mul Y (G.pub v) else G.pub v
        let Z : W ⊕ W := if X' = X then .inr Ys else .inl (G.exp X' v)
        let tC := trs.trCert (trs.tr1 x.1 r.peer x.2 X' Ys) l.1.1
        (Sg.sign l.1.2 tC).bind fun σ =>
          (sro G O X l.2.c.ro ⟨.sfin, trs.trCV tC σ, Z⟩).bind fun sf =>
            (sro G O X sf.2 ⟨.cfin, trs.trSF (trs.trCV tC σ) sf.1, Z⟩).map fun cf =>
              let imp := decide (shareR G X s (x.1, r.peer) ≠ some X')
              (.inr (.srvMsg (some (Ys, l.1.1, σ, sf.1))),
                { l.2 with
                  c := { l.2.c with
                    st := if imp then impStepOf srvImp l.2.c.st x else l.2.c.st
                    srv := Function.update l.2.c.srv x
                      (some (trs.trSF (trs.trCV tC σ) sf.1, Z, cf.1))
                    log := Function.update l.2.c.log x.2 (tC :: l.2.c.log x.2)
                    ro := cf.2 }
                  f := if imp then impStepOf srvImp l.2.f x else l.2.f
                  vs := if X' = X then v :: l.2.vs else l.2.vs })
    else PMF.pure (.inr (.srvMsg none), s)
  | none => PMF.pure (.inr (.srvMsg none), s)

/-- `cliRecv` at the client session `x` in the world of the reduction: the check of
`cliCheckK` with the filter, on the symbolic table, and the completion `deliverR`. -/
noncomputable def cliRecvR (s : RW S W Tr VK SK Sec) (x : Inst) (Y' : W) (σ : Sig) (sf : Sec) :
    PMF (TOOut W VK SK Sig Sec × RW S W Tr VK SK Sec) :=
  match s.c.st.recs x, s.c.eph x with
  | some r, some o =>
    if r.role = .initiator ∧ r.key.isNone then
      (rlt Sg s r.peer).bind fun l =>
        let Xc : W := match o with
          | some xs => G.pub xs
          | none => X
        let Z : W ⊕ W := match o with
          | some xs => .inl (G.exp Y' xs)
          | none => .inr Y'
        let tC := trs.trCert (trs.tr1 x.1 x.2 r.peer Xc Y') l.1.1
        (sro G O X l.2.c.ro ⟨.sfin, trs.trCV tC σ, Z⟩).bind fun sv =>
          if Sg.verify l.1.1 tC σ ∧ sf = sv.1 ∧
              (l.2.c.st.corrupt r.peer || decide (tC ∈ l.2.c.log r.peer)) then
            (sro G O X sv.2 ⟨.cfin, trs.trSF (trs.trCV tC σ) sf, Z⟩).bind fun cf =>
              deliverR G trs O X { l.2 with c := { l.2.c with ro := cf.2 } } x
                (trs.trSF (trs.trCV tC σ) sf) Z cf.1 (.cliFin (some cf.1))
          else PMF.pure (.inr (.cliFin none), { l.2 with c := { l.2.c with ro := sv.2 } })
    else PMF.pure (.inr (.cliFin none), s)
  | _, _ => PMF.pure (.inr (.cliFin none), s)

/-- **The world of the reduction** for the `i`-th client share, on the challenge `(X, Y)` with
the decision oracle `O`: a copy of the simulated world with the challenge embedded. -/
noncomputable def redO (s : RW S W Tr VK SK Sec) :
    TOEv W Tr Sig Sec → PMF (TOOut W VK SK Sig Sec × RW S W Tr VK SK Sec)
  | .inl (.newSession sid pid peer role) =>
    PMF.pure (.inl .ok, { s with c := { s.c with st := addSession s.c.st (sid, pid) peer role }
                                 f := addSession s.f (sid, pid) peer role })
  | .inl (.getKey sid pid) => PMF.pure (.inl (.key (keyOf s.f (sid, pid))), s)
  | .inr .idle => PMF.pure (.inr .ack, s)
  | .inr .poll => PMF.pure (.inr (.notice (pollStep s.c.st).2),
      { s with c := { s.c with st := (pollStep s.c.st).1 } })
  | .inr (.pub pid) => (rlt Sg s pid).map fun l => (.inr (.pub l.1.1), l.2)
  | .inr (.corrupt pid) =>
    if Pending s.c pid then PMF.pure (.inr .ack, s) else
      (rlt Sg s pid).map fun l =>
        (.inr (.secret l.1.2), { l.2 with c := { l.2.c with st := corruptStep l.2.c.st pid }
                                          f := corruptStep l.2.f pid })
  | .inr (.hello sid pid) =>
    match s.c.st.recs (sid, pid) with
    | some r =>
      if r.role = .initiator then
        match s.c.eph (sid, pid) with
        | some _ => PMF.pure (.inr (.share (shareR G X s (sid, pid))), s)
        | none =>
          if s.hellos = i then
            PMF.pure (.inr (.share (some X)),
              { s with c := { s.c with eph := Function.update s.c.eph (sid, pid) (some none) }
                       hellos := s.hellos + 1 })
          else
            (PMF.uniformFintype S).map fun xs =>
              (.inr (.share (some (G.pub xs))),
                { s with c := { s.c with eph := Function.update s.c.eph (sid, pid) (some xs) }
                         hellos := s.hellos + 1 })
      else PMF.pure (.inr (.share none), s)
    | none => PMF.pure (.inr (.share none), s)
  | .inr (.srvRecv sid pid X') => srvRecvR G Sg trs O X Y s (sid, pid) X'
  | .inr (.cliRecv sid pid Y' σ sf) => cliRecvR G Sg trs O X s (sid, pid) Y' σ sf
  | .inr (.srvFin sid pid cfin) =>
    match srvFinCheck s.c (sid, pid) cfin with
    | some p => deliverR G trs O X s (sid, pid) p.1 p.2.1 p.2.2 .ack
    | none => PMF.pure (.inr .ack, s)
  | .inr (.kdf z) => (sro G O X s.c.ro ⟨z.lbl, z.tr, .inl z.dhe⟩).map fun p =>
      (.inr (.hash p.1), { s with c := { s.c with ro := p.2 } })

/-- The initial state of the world of the reduction. -/
def rwInit : RW S W Tr VK SK Sec :=
  ⟨⟨initSt, fun _ => none, fun _ => none, fun _ => none, fun _ => [], []⟩, fun _ => none, initSt,
    0, []⟩

/-- **The extraction** of the reduction: `W · X^{-v}` for the first entry of the symbolic table
with a known value `W` and the first recorded exponent `v` such that `O` accepts
`(X, Y · g^v, W)`; `X` when there is none. -/
def extractT (s : RW S W Tr VK SK Sec) : W :=
  match (s.c.ro.filterMap fun p => match p.1.dhe with
      | .inl w => (s.vs.find? fun v => O X (G.mul Y (G.pub v)) w).map fun v =>
          G.mul w (G.exp X (-v))
      | .inr _ => none).head? with
  | some w => w
  | none => X

/-- **The output distribution of the reduction**: the extraction from the final state of a run of
`B` against the world of the reduction. -/
noncomputable def tlsGdhOut (B : OracleAdv (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) Bool) :
    PMF W :=
  (OracleAdv.run (redO G Sg trs i O X Y) B rwInit).map fun p => extractT G O X Y p.2

/-- The symbolic table and the rerandomisation exponents of `s` are kept in `s'`. -/
def RMono (s s' : RW S W Tr VK SK Sec) : Prop :=
  (∀ p ∈ s.c.ro, p ∈ s'.c.ro) ∧ ∀ v ∈ s.vs, v ∈ s'.vs

omit [Field S] [Fintype S] [SampleableType W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- `RMono` is transitive. -/
theorem RMono.trans {s s' s'' : RW S W Tr VK SK Sec} (h : RMono s s') (h' : RMono s' s'') :
    RMono s s'' :=
  ⟨fun p hp => h'.1 p (h.1 p hp), fun v hv => h'.2 v (h.2 v hv)⟩

omit [Field S] [Fintype S] [SampleableType W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- `RMono` is reflexive. -/
theorem rMono_refl (s : RW S W Tr VK SK Sec) : RMono s s := ⟨fun _ h => h, fun _ h => h⟩

omit [Fintype S] [DecidableEq Sec] [Inhabited Sec] in
/-- The symbolic key derivation extends the table. -/
theorem sro_mono (tb : List (TInp Tr (W ⊕ W) × Sec)) (j : TInp Tr (W ⊕ W)) :
    ∀ z ∈ (sro G O X tb j).support, ∀ p ∈ tb, p ∈ z.2 := by
  intro z hz p hp
  unfold sro at hz
  split at hz
  · rw [PMF.support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hp
  · rw [PMF.support_map] at hz
    obtain ⟨v, -, rfl⟩ := hz
    exact List.mem_cons_of_mem _ hp

omit [Fintype S] [DecidableEq Sec] [Inhabited Sec] in
/-- The symbolic keys extend the table. -/
theorem skeys_mono (tb : List (TInp Tr (W ⊕ W) × Sec)) (tSF : Tr) (Z : W ⊕ W) (cf : Sec) :
    ∀ z ∈ (skeys G trs O X tb tSF Z cf).support, ∀ p ∈ tb, p ∈ z.2 := by
  intro z hz p hp
  simp only [skeys, PMF.support_bind, PMF.support_map, Set.mem_iUnion, Set.mem_image] at hz
  obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := hz
  exact sro_mono G O X _ _ d hd p (sro_mono G O X _ _ c hc p (sro_mono G O X _ _ b hb p
    (sro_mono G O X _ _ a ha p hp)))

omit [Field S] [Fintype S] [SampleableType W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- The signing key pair at its first use keeps the table and the exponents. -/
theorem rlt_mono (s : RW S W Tr VK SK Sec) (pid : PartyId) :
    ∀ z ∈ (rlt Sg s pid).support, z.2.c.ro = s.c.ro ∧ z.2.vs = s.vs := by
  intro z hz
  unfold rlt at hz
  split at hz
  · rw [PMF.support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨rfl, rfl⟩
  · rw [PMF.support_map] at hz
    obtain ⟨l, -, rfl⟩ := hz
    exact ⟨rfl, rfl⟩

omit [Fintype S] [DecidableEq Sec] in
/-- The completion in the world of the reduction keeps the table and the exponents. -/
theorem deliverR_mono (s : RW S W Tr VK SK Sec) (x : Inst) (tSF : Tr) (Z : W ⊕ W) (cf : Sec)
    (o : TOut W VK SK Sig Sec) :
    ∀ z ∈ (deliverR G trs O X s x tSF Z cf o).support, RMono s z.2 := by
  intro z hz
  unfold deliverR at hz
  split at hz
  · rename_i r _
    by_cases hE : Exposed s.c.st x r
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hE)] at hz
      simp only [PMF.support_bind, PMF.support_map, Set.mem_iUnion, Set.mem_image] at hz
      obtain ⟨k, hk, kf, -, rfl⟩ := hz
      exact ⟨fun p hp => skeys_mono G trs O X _ _ _ _ k hk p hp, fun _ h => h⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hE)] at hz
      simp only [PMF.support_map, Set.mem_image] at hz
      obtain ⟨kf, -, rfl⟩ := hz
      exact ⟨fun _ h => h, fun _ h => h⟩
  · rw [PMF.support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact rMono_refl _

omit [DecidableEq Sec] [Inhabited Sec] in
/-- `srvRecv` in the world of the reduction keeps the table and the exponents. -/
theorem srvRecvR_mono (s : RW S W Tr VK SK Sec) (x : Inst) (X' : W) :
    ∀ z ∈ (srvRecvR G Sg trs O X Y s x X').support, RMono s z.2 := by
  intro z hz
  unfold srvRecvR at hz
  split at hz
  · rename_i r _
    by_cases hc : r.role = .responder ∧ r.key.isNone ∧ (s.c.srv x).isNone
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at hz
      simp only [PMF.support_bind, PMF.support_map, Set.mem_iUnion, Set.mem_image] at hz
      obtain ⟨l, hl, v, -, σ, -, sf, hsf, cf, hcf, rfl⟩ := hz
      obtain ⟨hro, hvs⟩ := rlt_mono Sg s _ l hl
      refine ⟨fun p hp => ?_, fun w hw => ?_⟩
      · rw [← hro] at hp
        exact sro_mono G O X _ _ cf hcf p (sro_mono G O X _ _ sf hsf p hp)
      · rw [← hvs] at hw
        split_ifs <;> simp [hw]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at hz
      rw [PMF.support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact rMono_refl _
  · rw [PMF.support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact rMono_refl _

omit [Fintype S] in
/-- `cliRecv` in the world of the reduction keeps the table and the exponents. -/
theorem cliRecvR_mono (s : RW S W Tr VK SK Sec) (x : Inst) (Y' : W) (σ : Sig) (sf : Sec) :
    ∀ z ∈ (cliRecvR G Sg trs O X s x Y' σ sf).support, RMono s z.2 := by
  intro z hz
  unfold cliRecvR at hz
  split at hz
  · rename_i r o _ _
    by_cases hc : r.role = .initiator ∧ r.key.isNone
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at hz
      simp only [PMF.mem_support_bind_iff] at hz
      obtain ⟨l, hl, sv, hsv, hz⟩ := hz
      obtain ⟨hro, hvs⟩ := rlt_mono Sg s _ l hl
      have hsv' : ∀ p ∈ s.c.ro, p ∈ sv.2 := fun p hp =>
        sro_mono G O X _ _ sv hsv p (by rw [hro]; exact hp)
      split_ifs at hz
      · simp only [PMF.mem_support_bind_iff] at hz
        obtain ⟨cf, hcf, hz⟩ := hz
        refine (?_ : RMono s _).trans (deliverR_mono G trs O X _ x _ _ _ _ z hz)
        exact ⟨fun p hp => sro_mono G O X _ _ cf hcf p (hsv' p hp),
          fun w hw => by rw [← hvs] at hw; exact hw⟩
      · rw [PMF.support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact ⟨hsv', fun w hw => by rw [← hvs] at hw; exact hw⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at hz
      rw [PMF.support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact rMono_refl _
  · rw [PMF.support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact rMono_refl _

/-- **The world of the reduction keeps its table and its exponents.** -/
theorem redO_mono (s : RW S W Tr VK SK Sec) (e : TOEv W Tr Sig Sec) :
    ∀ z ∈ (redO G Sg trs i O X Y s e).support, RMono s z.2 := by
  intro z hz
  have hpure : ∀ (o : TOOut W VK SK Sig Sec) (s' : RW S W Tr VK SK Sec), s'.c.ro = s.c.ro →
      s'.vs = s.vs → z ∈ (PMF.pure (o, s')).support → RMono s z.2 := by
    intro o s' h1 h2 hz
    rw [PMF.support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨fun p hp => by rw [h1]; exact hp, fun v hv => by rw [h2]; exact hv⟩
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) |
    (_ | _ | pid | pid | ⟨sid, pid⟩ | ⟨sid, pid, X'⟩ | ⟨sid, pid, Y', σ, sf⟩ | ⟨sid, pid, cfin⟩ |
      w)
  · simp only [redO] at hz
    exact hpure _ _ (by rfl) (by rfl) hz
  · exact hpure _ _ (by rfl) (by rfl) hz
  · exact hpure _ _ (by rfl) (by rfl) hz
  · simp only [redO] at hz
    exact hpure _ _ (by rfl) (by rfl) hz
  · simp only [redO, PMF.support_map, Set.mem_image] at hz
    obtain ⟨l, hl, rfl⟩ := hz
    obtain ⟨h1, h2⟩ := rlt_mono Sg s pid l hl
    exact ⟨fun p hp => by rw [h1]; exact hp, fun v hv => by rw [h2]; exact hv⟩
  · simp only [redO] at hz
    split_ifs at hz
    · exact hpure _ _ (by rfl) (by rfl) hz
    · simp only [PMF.support_map, Set.mem_image] at hz
      obtain ⟨l, hl, rfl⟩ := hz
      obtain ⟨h1, h2⟩ := rlt_mono Sg s pid l hl
      exact ⟨fun p hp => by rw [h1]; exact hp, fun v hv => by rw [h2]; exact hv⟩
  · simp only [redO] at hz
    repeat' split at hz
    all_goals first
      | exact hpure _ _ (by rfl) (by rfl) hz
      | (simp only [PMF.support_map, Set.mem_image] at hz
         obtain ⟨_, _, rfl⟩ := hz
         exact ⟨fun _ h => h, fun _ h => h⟩)
  · exact srvRecvR_mono G Sg trs O X Y s _ _ z hz
  · exact cliRecvR_mono G Sg trs O X s _ _ _ _ z hz
  · simp only [redO] at hz
    split at hz
    · exact deliverR_mono G trs O X s _ _ _ _ _ z hz
    · exact hpure _ _ (by rfl) (by rfl) hz
  · simp only [redO, PMF.support_map, Set.mem_image] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    exact ⟨fun q hq => sro_mono G O X _ _ p hp q hq, fun _ h => h⟩

end Red

/-! ## Couplings of oracle steps -/

section Coupling

/-- `p` and `q` are coupled for `R`: a joint distribution with marginals `p` and `q` whose
support lies on `R`. -/
def Coupled {α β : Type} (p : PMF α) (q : PMF β) (R : α → β → Prop) : Prop :=
  ∃ J : PMF (α × β), J.map Prod.fst = p ∧ J.map Prod.snd = q ∧ ∀ z ∈ J.support, R z.1 z.2

/-- A coupling for a relation is a coupling for every weaker relation. -/
theorem Coupled.mono {α β : Type} {p : PMF α} {q : PMF β} {R R' : α → β → Prop}
    (h : Coupled p q R) (hR : ∀ a b, R a b → R' a b) : Coupled p q R' := by
  obtain ⟨J, h1, h2, h3⟩ := h
  exact ⟨J, h1, h2, fun z hz => hR _ _ (h3 z hz)⟩

/-- Two point masses at related points are coupled. -/
theorem coupled_pure {α β : Type} {R : α → β → Prop} {a : α} {b : β} (h : R a b) :
    Coupled (PMF.pure a) (PMF.pure b) R :=
  ⟨PMF.pure (a, b), by rw [PMF.pure_map], by rw [PMF.pure_map], fun z hz => by
    rw [PMF.mem_support_pure_iff] at hz; subst hz; exact h⟩

/-- A distribution is coupled with itself for equality. -/
theorem coupled_same {α : Type} (p : PMF α) : Coupled p p (· = ·) := by
  refine ⟨p.map fun a => (a, a), ?_, ?_, ?_⟩
  · rw [PMF.map_comp]; exact PMF.map_id p
  · rw [PMF.map_comp]; exact PMF.map_id p
  · intro z hz
    rw [PMF.mem_support_map_iff] at hz
    obtain ⟨a, -, rfl⟩ := hz
    rfl

/-- The independent product couples two distributions for membership in their supports. -/
theorem coupled_indep {α β : Type} (p : PMF α) (q : PMF β) :
    Coupled p q (fun a b => a ∈ p.support ∧ b ∈ q.support) := by
  refine ⟨p.bind fun a => q.map fun b => (a, b), ?_, ?_, ?_⟩
  · have hc : ∀ a : α, PMF.map (fun _ : β => a) q = PMF.pure a := fun a => PMF.map_const q a
    rw [PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def, hc, PMF.bind_pure]
  · have hc : PMF.map (fun x : β => x) q = q := PMF.map_id q
    rw [PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def, hc, PMF.bind_const]
  · intro z hz
    simp only [PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hz
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    exact ⟨ha, hb⟩

/-- A bind depends only on the continuation on the support. -/
theorem bind_congr_supp {α β : Type} (p : PMF α) (f g : α → PMF β)
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  ext b
  simp only [PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · simp [(PMF.apply_eq_zero_iff _ _).2 ha]

/-- Couplings compose along binds: coupled prefixes and, at related points, coupled
continuations give coupled binds. -/
theorem coupled_bind {α β α' β' : Type} {p : PMF α} {q : PMF β} {R : α → β → Prop}
    {f : α → PMF α'} {g : β → PMF β'} {S : α' → β' → Prop} (h : Coupled p q R)
    (hf : ∀ a b, R a b → Coupled (f a) (g b) S) : Coupled (p.bind f) (q.bind g) S := by
  classical
  obtain ⟨J, h1, h2, h3⟩ := h
  let k : α × β → PMF (α' × β') := fun z =>
    if hz : R z.1 z.2 then (hf z.1 z.2 hz).choose else (f z.1).bind fun a => (g z.2).map (a, ·)
  have hk : ∀ z ∈ J.support, (k z).map Prod.fst = f z.1 ∧ (k z).map Prod.snd = g z.2 ∧
      ∀ w ∈ (k z).support, S w.1 w.2 := fun z hz => by
    simp only [k, h3 z hz, ↓reduceDIte]
    exact (hf z.1 z.2 (h3 z hz)).choose_spec
  refine ⟨J.bind k, ?_, ?_, ?_⟩
  · rw [PMF.map_bind, ← h1, PMF.bind_map]
    exact bind_congr_supp _ _ _ fun z hz => (hk z hz).1
  · rw [PMF.map_bind, ← h2, PMF.bind_map]
    exact bind_congr_supp _ _ _ fun z hz => (hk z hz).2.1
  · intro w hw
    rw [PMF.mem_support_bind_iff] at hw
    obtain ⟨z, hz, hw⟩ := hw
    exact (hk z hz).2.2 w hw

/-- Images of coupled distributions are coupled for the relation pulled back along the maps. -/
theorem coupled_map {α β α' β' : Type} {p : PMF α} {q : PMF β} {R : α' → β' → Prop}
    (f : α → α') (g : β → β') (h : Coupled p q fun a b => R (f a) (g b)) :
    Coupled (p.map f) (q.map g) R := by
  rw [← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
  exact coupled_bind h fun a b hab => coupled_pure hab

variable {D R σ₁ σ₂ α : Type}

open Classical in
/-- **A coupling of the steps up to a bad transition, for an output event.** Let every call of
`O₁` from `s₁` and of `O₂` from `s₂` with `I s₁ s₂` be coupled so that the second call is bad or
the answers agree and `I` holds after. Then the probability of an output event under `O₁` is at
most the probability of the event or of the flag in the flagged run of `O₂`, and the probability
of the event without the flag under `O₂` is at most its probability under `O₁`. -/
theorem run_le_of_coupled (O₁ : σ₁ → D → PMF (R × σ₁)) (O₂ : σ₂ → D → PMF (R × σ₂))
    (bad : σ₂ → D → R × σ₂ → Prop) (I : σ₁ → σ₂ → Prop)
    (hc : ∀ s₁ s₂ d, I s₁ s₂ → Coupled (O₁ s₁ d) (O₂ s₂ d)
      fun z₁ z₂ => bad s₂ d z₂ ∨ (z₁.1 = z₂.1 ∧ I z₁.2 z₂.2))
    (A : OracleAdv D R α) (E : Set α) : ∀ s₁ s₂, I s₁ s₂ →
      (OracleAdv.run O₁ A s₁).toOuterMeasure {x | x.1 ∈ E} ≤
        (OracleAdv.run (OracleAdv.flagWhen bad O₂) A (s₂, false)).toOuterMeasure
          {y | y.1 ∈ E ∨ y.2.2 = true} ∧
      (OracleAdv.run (OracleAdv.flagWhen bad O₂) A (s₂, false)).toOuterMeasure
          {y | y.1 ∈ E ∧ y.2.2 = false} ≤
        (OracleAdv.run O₁ A s₁).toOuterMeasure {x | x.1 ∈ E} := by
  have htrue : ∀ (B : OracleAdv D R α) (s : σ₂),
      ∀ y ∈ (OracleAdv.run (OracleAdv.flagWhen bad O₂) B (s, true)).support, y.2.2 = true :=
    fun B s => OracleAdv.run_support_inv _ (fun t => t.2 = true) (fun t d x ht hx => by
      simp only [OracleAdv.flagWhen, PMF.support_map, Set.mem_image] at hx
      obtain ⟨z, -, rfl⟩ := hx
      simp [ht]) B (s, true) rfl
  induction A with
  | ret a =>
    intro s₁ s₂ _
    simp only [OracleAdv.run_ret, PMF.toOuterMeasure_pure_apply, Set.mem_ofPred_eq]
    by_cases ha : a ∈ E <;> simp [ha]
  | rand p k ih =>
    intro s₁ s₂ hs
    simp only [OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply]
    exact ⟨ENNReal.tsum_le_tsum fun b => by gcongr; exact (ih b s₁ s₂ hs).1,
      ENNReal.tsum_le_tsum fun b => by gcongr; exact (ih b s₁ s₂ hs).2⟩
  | query d k ih =>
    intro s₁ s₂ hs
    obtain ⟨J, h1, h2, h3⟩ := hc s₁ s₂ d hs
    simp only [OracleAdv.run_query, OracleAdv.flagWhen]
    rw [← h1, ← h2, PMF.map_comp, PMF.bind_map, PMF.bind_map]
    simp only [PMF.toOuterMeasure_bind_apply]
    have hz : ∀ z ∈ J.support, ∀ T : Set (α × σ₂ × Bool), {y | y.2.2 = true} ⊆ T →
        bad s₂ d z.2 → (OracleAdv.run (OracleAdv.flagWhen bad O₂) (k z.2.1)
          (z.2.2, false || decide (bad s₂ d z.2))).toOuterMeasure T = 1 := by
      intro z _ T hT hb
      rw [PMF.toOuterMeasure_apply_eq_one_iff]
      intro y hy
      exact hT (htrue _ _ y (by simpa [hb] using hy))
    have hz0 : ∀ z ∈ J.support, bad s₂ d z.2 → (OracleAdv.run (OracleAdv.flagWhen bad O₂)
        (k z.2.1) (z.2.2, false || decide (bad s₂ d z.2))).toOuterMeasure
          {y | y.1 ∈ E ∧ y.2.2 = false} = 0 := by
      intro z _ hb
      rw [PMF.toOuterMeasure_apply_eq_zero_iff]
      refine Set.disjoint_left.mpr fun y hy hy' => ?_
      have := htrue _ _ y (by simpa [hb] using hy)
      simp_all
    refine ⟨ENNReal.tsum_le_tsum fun z => ?_, ENNReal.tsum_le_tsum fun z => ?_⟩
    · by_cases hzs : z ∈ J.support
      · gcongr
        by_cases hb : bad s₂ d z.2
        · simp only [Function.comp_apply]
          rw [hz z hzs {y | y.1 ∈ E ∨ y.2.2 = true} (fun y hy => Or.inr hy) hb]
          exact X3DHSquareGDH.toOuterMeasure_le_one _ _
        · rcases h3 z hzs with hb' | ⟨he, hI⟩
          · exact absurd hb' hb
          simp only [Function.comp_apply, hb, decide_false, Bool.or_false, he]
          exact (ih z.2.1 z.1.2 z.2.2 hI).1
      · simp [(PMF.apply_eq_zero_iff _ _).2 hzs]
    · by_cases hzs : z ∈ J.support
      · gcongr
        by_cases hb : bad s₂ d z.2
        · simp only [Function.comp_apply]
          rw [hz0 z hzs hb]
          exact zero_le
        · rcases h3 z hzs with hb' | ⟨he, hI⟩
          · exact absurd hb' hb
          simp only [Function.comp_apply, hb, decide_false, Bool.or_false, he]
          exact (ih z.2.1 z.1.2 z.2.2 hI).2
      · simp [(PMF.apply_eq_zero_iff _ _).2 hzs]

open Classical in
/-- **Up to a bad transition, through a coupling of the steps.** Under the hypothesis of
`run_le_of_coupled`, the probabilities that the adversary outputs `true` against `O₁` from `s₁`
and against `O₂` from `s₂` differ by at most the probability that the flagged run of `O₂` sets
the flag. -/
theorem absDiff_le_of_coupled (O₁ : σ₁ → D → PMF (R × σ₁)) (O₂ : σ₂ → D → PMF (R × σ₂))
    (bad : σ₂ → D → R × σ₂ → Prop) (I : σ₁ → σ₂ → Prop)
    (hc : ∀ s₁ s₂ d, I s₁ s₂ → Coupled (O₁ s₁ d) (O₂ s₂ d)
      fun z₁ z₂ => bad s₂ d z₂ ∨ (z₁.1 = z₂.1 ∧ I z₁.2 z₂.2))
    (A : OracleAdv D R Bool) (s₁ : σ₁) (s₂ : σ₂) (hs : I s₁ s₂) :
    absDiff (((OracleAdv.run O₁ A s₁).map Prod.fst) true)
        (((OracleAdv.run O₂ A s₂).map Prod.fst) true) ≤
      (OracleAdv.run (OracleAdv.flagWhen bad O₂) A (s₂, false)).toOuterMeasure
        {y | y.2.2 = true} := by
  obtain ⟨h1, h2⟩ := run_le_of_coupled O₁ O₂ bad I hc A {true} s₁ s₂ hs
  set F := OracleAdv.run (OracleAdv.flagWhen bad O₂) A (s₂, false)
  have hP₂ : ((OracleAdv.run O₂ A s₂).map Prod.fst) true =
      F.toOuterMeasure {y | y.1 ∈ ({true} : Set Bool)} := by
    rw [map_fst_apply_true, ← OracleAdv.run_flagWhen_map bad O₂ A s₂ false,
      PMF.toOuterMeasure_map_apply]
    rfl
  rw [map_fst_apply_true, hP₂]
  refine max_le (tsub_le_iff_left.mpr ?_) (tsub_le_iff_left.mpr ?_)
  · refine h1.trans ((MeasureTheory.measure_mono ?_).trans (MeasureTheory.measure_union_le _ _))
    intro y hy
    exact hy
  · refine (MeasureTheory.measure_mono ?_).trans ((MeasureTheory.measure_union_le _ _).trans
      (add_le_add h2 le_rfl))
    intro y hy
    cases hb : y.2.2
    · exact Or.inl ⟨hy, hb⟩
    · exact Or.inr hb

/-- A run from a state of an invariant ends in the invariant. -/
theorem run_toOuterMeasure_inv (O : σ₂ → D → PMF (R × σ₂)) (P : σ₂ → Prop)
    (hP : ∀ s d, P s → ∀ x ∈ (O s d).support, P x.2) (A : OracleAdv D R α) (s : σ₂)
    (hs : P s) : (OracleAdv.run O A s).toOuterMeasure {z | P z.2} = 1 :=
  (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr fun z hz =>
    OracleAdv.run_support_inv O P (fun s d x hs hx => hP s d hs x hx) A s hs z hz

open Classical in
/-- A flagged run from a state of an invariant on which the bad event fails never sets the
flag. -/
theorem run_flag_dead (O : σ₁ → D → PMF (R × σ₁)) (Dead bad : σ₁ → Prop)
    (hdead : ∀ s d, Dead s → ∀ x ∈ (O s d).support, Dead x.2) (hdb : ∀ s, Dead s → ¬ bad s)
    (A : OracleAdv D R α) (s : σ₁) (hs : Dead s) :
    (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => bad x.2) O) A (s, false)).toOuterMeasure
      {y | y.2.2 = true} = 0 := by
  rw [PMF.toOuterMeasure_apply_eq_zero_iff]
  refine Set.disjoint_left.mpr fun y hy hy' => ?_
  have := OracleAdv.run_support_inv _ (fun t => Dead t.1 ∧ t.2 = false) (fun t d x ht hx => by
    simp only [OracleAdv.flagWhen, PMF.support_map, Set.mem_image] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact ⟨hdead _ d ht.1 z hz, by simp [ht.2, hdb _ (hdead _ d ht.1 z hz)]⟩) A (s, false)
    ⟨hs, rfl⟩ y hy
  simp_all

open Classical in
/-- **A bad flag below a final event, through a coupling of the steps.** Let `Dead` be kept by
`O₁` and exclude `bad₁`, let `Good` be kept by `O₂`, and let every call of `O₁` from `s₁` and of
`O₂` from `s₂` with `I s₁ s₂` be coupled so that the first reaches `Dead`, or the second reaches
`Good`, or the answers agree, `I` holds after and `bad₁` fails. Then the run of `O₁` sets the flag
of `bad₁` at most with the probability that the run of `O₂` ends in `Good`. -/
theorem flag_le_final_of_coupled (O₁ : σ₁ → D → PMF (R × σ₁)) (O₂ : σ₂ → D → PMF (R × σ₂))
    (bad₁ Dead : σ₁ → Prop) (Good : σ₂ → Prop) (I : σ₁ → σ₂ → Prop)
    (hdead : ∀ s d, Dead s → ∀ x ∈ (O₁ s d).support, Dead x.2) (hdb : ∀ s, Dead s → ¬ bad₁ s)
    (hgood : ∀ s d, Good s → ∀ x ∈ (O₂ s d).support, Good x.2)
    (hc : ∀ s₁ s₂ d, I s₁ s₂ → Coupled (O₁ s₁ d) (O₂ s₂ d) fun z₁ z₂ =>
      Dead z₁.2 ∨ Good z₂.2 ∨ (z₁.1 = z₂.1 ∧ I z₁.2 z₂.2 ∧ ¬ bad₁ z₁.2))
    (A : OracleAdv D R α) : ∀ s₁ s₂, I s₁ s₂ →
      (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => bad₁ x.2) O₁) A (s₁, false)).toOuterMeasure
          {y | y.2.2 = true} ≤ (OracleAdv.run O₂ A s₂).toOuterMeasure {z | Good z.2} := by
  induction A with
  | ret a =>
    intro s₁ s₂ _
    rw [OracleAdv.run_ret, PMF.toOuterMeasure_pure_apply]
    simp
  | rand p k ih =>
    intro s₁ s₂ hs
    rw [OracleAdv.run_rand, OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply,
      PMF.toOuterMeasure_bind_apply]
    exact ENNReal.tsum_le_tsum fun b => by gcongr; exact ih b s₁ s₂ hs
  | query d k ih =>
    intro s₁ s₂ hs
    obtain ⟨J, h1, h2, h3⟩ := hc s₁ s₂ d hs
    rw [OracleAdv.run_query, OracleAdv.run_query, OracleAdv.flagWhen, ← h1, ← h2, PMF.map_comp,
      PMF.bind_map, PMF.bind_map, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
    refine ENNReal.tsum_le_tsum fun z => ?_
    by_cases hzs : z ∈ J.support
    · gcongr
      simp only [Function.comp_apply, Bool.false_or]
      rcases h3 z hzs with hd | hg | ⟨he, hI, hb⟩
      · rw [decide_eq_false (hdb _ hd), run_flag_dead O₁ Dead bad₁ hdead hdb _ _ hd]
        exact zero_le
      · rw [run_toOuterMeasure_inv O₂ Good hgood _ _ hg]
        exact X3DHSquareGDH.toOuterMeasure_le_one _ _
      · rw [decide_eq_false hb, he]
        exact ih z.2.1 z.1.2 z.2.2 hI
    · simp [(PMF.apply_eq_zero_iff _ _).2 hzs]

end Coupling

/-! ## The coupling of the filtered and the simulated world -/

section Rel

variable {S W Tr VK SK Sig Sec : Type} [Fintype S] [Nonempty S] [DecidableEq W]
  [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec] [Nonempty Sec] [Inhabited Sec]
  (A : TLSAlg S W Tr VK SK Sig Sec)

/-- The transcript `t` up to server Finished is a transcript of the session `x` with the role
`role` and the peer `peer`. -/
def TrOf (x : Inst) (role : Role) (peer : PartyId) (t : Tr) : Prop :=
  ∃ X Y vk σ sf, t = A.trSF (A.trCV (A.trCert (A.tr1 x.1
    (if role = .initiator then x.2 else peer) (if role = .initiator then peer else x.2) X Y)
    vk) σ) sf

/-- The input `i` is an external stage input of a session whose key the functionality chose. -/
def XIn (t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) (i : TInp Tr W) : Prop :=
  ∃ y r ip, t.2.recs y = some r ∧ r.status = .completed ∧ t.1.2.1 y = some ip ∧ ExtIn A ip i

/-- The components of a state that the filtered world and the copy of the simulator share. -/
def comm (s : TRSt S W Tr VK SK Sec) :=
  (s.lt, s.eph, s.srv, s.log, s.st.corrupt, s.st.notices, s.st.cursor)

/-- The shape of a record seen by the copy: peer, role and whether a key is set. -/
def shp {K : Type} (r : Rec K) : PartyId × Role × Bool := (r.peer, r.role, r.key.isSome)

/-- The shape of a record with its key. -/
def shk {K : Type} (r : Rec K) : PartyId × Role × Option K := (r.peer, r.role, r.key)

/-- **The coupling invariant** between a state `s` of the filtered world and a state `t` of the
simulated world. The shared components agree; the records agree in peer and role, the keys of the
filtered world are the keys of the functionality, the copy has a key where the functionality has
one, and a record without key has the same status in the copy and in the functionality. The
tables of the key derivation agree outside the external stage inputs of the sessions whose key
the functionality chose; the copy's table holds none of these inputs; the table of the filtered
world holds the key of each such session at its stage inputs. A server session that answered has
its client Finished in the table and a transcript of its own. -/
structure Cpl (s : TRSt S W Tr VK SK Sec) (t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) :
    Prop where
  /-- The simulator stores no output. -/
  ph : t.1.2.2 = none
  /-- The shared components agree. -/
  com : comm s = comm t.1.1
  /-- The functionality and the copy have the same corrupt parties. -/
  fcor : t.2.corrupt = t.1.1.st.corrupt
  /-- The records of the filtered world and of the copy have the same shape. -/
  rsc : ∀ x, (s.st.recs x).map shp = (t.1.1.st.recs x).map shp
  /-- The records of the filtered world and of the functionality agree with their keys. -/
  rsf : ∀ x, (s.st.recs x).map shk = (t.2.recs x).map shk
  /-- A record without key has the same status in the copy and in the functionality. -/
  rst : ∀ x rc rf, t.1.1.st.recs x = some rc → t.2.recs x = some rf → rf.key = none →
    rc.status = rf.status
  /-- The tables agree outside the external inputs of the sessions the functionality keyed. -/
  tab : ∀ i, ¬ XIn A t i → s.ro.lookup i = t.1.1.ro.lookup i
  /-- The copy's table holds no such external input. -/
  nohit : ∀ i, XIn A t i → t.1.1.ro.lookup i = none
  /-- A session the functionality keyed has its recorded input, a transcript of its own, and
  its key at its stage inputs in the table of the filtered world. -/
  comp : ∀ y r, t.2.recs y = some r → r.status = .completed → ∃ k ip cf, r.key = some k ∧
    t.1.2.1 y = some ip ∧ ip.lbl = .cap ∧ TrOf A y r.role r.peer ip.tr ∧
    s.ro.lookup ⟨.cap, ip.tr, ip.dhe⟩ = some k.1 ∧ s.ro.lookup ⟨.sap, ip.tr, ip.dhe⟩ = some k.2.1 ∧
    s.ro.lookup ⟨.exp, ip.tr, ip.dhe⟩ = some k.2.2.1 ∧
    s.ro.lookup ⟨.cfin, ip.tr, ip.dhe⟩ = some cf ∧
    s.ro.lookup ⟨.res, A.trCF ip.tr cf, ip.dhe⟩ = some k.2.2.2
  /-- A server session that answered has its client Finished in the table and a transcript of
  its own. -/
  srvI : ∀ x tSF Z cf, s.srv x = some (tSF, Z, cf) → s.ro.lookup ⟨.cfin, tSF, Z⟩ = some cf ∧
    ∃ r, s.st.recs x = some r ∧ r.role = .responder ∧ TrOf A x r.role r.peer tSF

/-- The initial state of the simulated game, unfolded. -/
theorem simInit_eq : simInit A = ((tInitK lazyKDF, fun _ => none, none), initSt) := rfl

/-- The initial states are coupled. -/
theorem cpl_init : Cpl A (tInitK lazyKDF) (simInit A) where
  ph := rfl
  com := rfl
  fcor := rfl
  rsc _ := rfl
  rsf _ := rfl
  rst _ _ _ h := by simp [simInit_eq, tInitK, initSt] at h
  tab _ _ := rfl
  nohit _ h := by
    obtain ⟨y, r, ip, h, -⟩ := h
    simp [simInit_eq, initSt] at h
  comp _ _ h := by simp [simInit_eq, initSt] at h
  srvI _ _ _ _ h := by simp [tInitK] at h

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- The table after a call of the random function with the fresh value `k`. -/
theorem roDet_lookup {D K : Type} [DecidableEq D] (T : List (D × K)) (i j : D) (k : K) :
    (roDet T i k).2.lookup j = if j = i then some (roDet T i k).1 else T.lookup j := by
  unfold roDet
  cases h : T.lookup i with
  | some v =>
    simp only
    split_ifs with hj
    · subst hj; exact h
    · rfl
  | none =>
    simp only [List.lookup]
    split_ifs with hj
    · simp_all
    · grind

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- The answer of the random function with the fresh value `k`. -/
theorem roDet_fst {D K : Type} [DecidableEq D] (T : List (D × K)) (i : D) (k : K) :
    (roDet T i k).1 = (T.lookup i).getD k := by
  unfold roDet
  cases T.lookup i <;> rfl

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- A recorded value stays recorded. -/
theorem roDet_lookup_of_some {D K : Type} [DecidableEq D] (T : List (D × K)) (i j : D) (k : K)
    {v : K} (h : T.lookup j = some v) : (roDet T i k).2.lookup j = some v := by
  rw [roDet_lookup, roDet_fst]
  split_ifs with hj
  · subst hj; rw [h]; rfl
  · exact h

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec]
  [Inhabited Sec] in
/-- The lazily sampled random function as the image of one fresh value. -/
theorem roAt_eq_roDet {D : Type} [DecidableEq D] (T : List (D × Sec)) (i : D) :
    CatCrypt.Crypto.PAKE.CPaceSquare.roAt T i = (PMF.uniformFintype Sec).map (roDet T i) :=
  (map_uniform_roDet T i).symm

omit [Fintype S] [Nonempty S] [DecidableEq Sec] [Fintype Sec] [Nonempty Sec] [Inhabited Sec] in
/-- A table entry at an external input of a session whose key the functionality chose is a
query at the key of a fresh session. -/
theorem keyHit_of {t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)} {i : TInp Tr W}
    (hX : XIn A t i) (hl : t.1.1.ro.lookup i ≠ none) : KeyHit A t := by
  obtain ⟨y, r, ip, h1, h2, h3, h4⟩ := hX
  obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hl
  unfold KeyHit
  grind

omit [Fintype S] [Nonempty S] [DecidableEq Sec] [Fintype Sec] [Nonempty Sec] [Inhabited Sec] in
/-- **A call of the random function outside the external inputs keeps the coupling**: both
tables receive the same fresh value. -/
theorem cpl_roDet {s : TRSt S W Tr VK SK Sec} {t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)}
    (h : Cpl A s t) {i : TInp Tr W} (hi : ¬ XIn A t i) (k : Sec) :
    (roDet s.ro i k).1 = (roDet t.1.1.ro i k).1 ∧
      Cpl A { s with ro := (roDet s.ro i k).2 }
        (({ t.1.1 with ro := (roDet t.1.1.ro i k).2 }, t.1.2.1, t.1.2.2), t.2) := by
  have hl := h.tab i hi
  have h1 : (roDet s.ro i k).1 = (roDet t.1.1.ro i k).1 := by rw [roDet_fst, roDet_fst, hl]
  refine ⟨h1, h.ph, h.com, h.fcor, h.rsc, h.rsf, h.rst, ?_, ?_, ?_, ?_⟩
  · intro j hj
    simp only [roDet_lookup, h1]
    split_ifs
    · rfl
    · exact h.tab j hj
  · intro j hj
    simp only [roDet_lookup]
    split_ifs with hji
    · subst hji; exact absurd hj hi
    · exact h.nohit j hj
  · intro y r hy hc
    obtain ⟨k', ip, cf, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ := h.comp y r hy hc
    exact ⟨k', ip, cf, h₁, h₂, h₃, h₄, roDet_lookup_of_some _ _ _ _ h₅,
      roDet_lookup_of_some _ _ _ _ h₆, roDet_lookup_of_some _ _ _ _ h₇,
      roDet_lookup_of_some _ _ _ _ h₈, roDet_lookup_of_some _ _ _ _ h₉⟩
  · intro x tSF Z cf hx
    obtain ⟨h₁, h₂⟩ := h.srvI x tSF Z cf hx
    exact ⟨roDet_lookup_of_some _ _ _ _ h₁, h₂⟩

/-- The oracle of the simulated game as the start of the simulator followed by at most one call
of the functionality. -/
theorem simO_core (t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) (e : TOEv W Tr Sig Sec) :
    simO A t e = (simCore A t.1 e).bind fun q => match q.2 with
      | .inl g => (PMF.uniformFintype (TKey Sec)).map fun kf =>
          (fwdOut .ack q.1.2.2 (fStepD t.2 g kf).2, (simReset q.1, (fStepD t.2 g kf).1))
      | .inr o => PMF.pure (.inr o, (q.1, t.2)) := by
  rw [simO_eq]
  simp only [withSubP, simStartP, PMF.map_bind, PMF.bind_map]
  congr 1
  funext q
  rcases q with ⟨s', g | o⟩
  · simp only [Function.comp_apply, liftDec, driveP, PMF.map_bind, PMF.pure_map]
    rw [PMF.bind_map, ← PMF.bind_pure_comp]
    rfl
  · simp only [Function.comp_apply, liftDec, driveP, PMF.pure_map]
    rfl

omit [Fintype S] [Nonempty S] [DecidableEq Sec] [Fintype Sec] [Nonempty Sec] [Inhabited Sec] in
/-- **A step that changes neither records, inputs nor tables keeps the coupling**, when the
shared components agree after it. -/
theorem cpl_frame {s s' : TRSt S W Tr VK SK Sec}
    {t t' : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)} (h : Cpl A s t)
    (hph : t'.1.2.2 = none) (hcom : comm s' = comm t'.1.1)
    (hcor : t'.2.corrupt = t'.1.1.st.corrupt) (hrs : s'.st.recs = s.st.recs)
    (hrc : t'.1.1.st.recs = t.1.1.st.recs) (hrf : t'.2.recs = t.2.recs)
    (hinp : t'.1.2.1 = t.1.2.1) (hro : s'.ro = s.ro) (hroc : t'.1.1.ro = t.1.1.ro)
    (hsrv : s'.srv = s.srv) : Cpl A s' t' := by
  have hX : ∀ i, XIn A t' i ↔ XIn A t i := fun i => by simp only [XIn, hrf, hinp]
  refine ⟨hph, hcom, hcor, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; rw [hrs, hrc]; exact h.rsc x
  · intro x; rw [hrs, hrf]; exact h.rsf x
  · intro x rc rf; rw [hrc, hrf]; exact h.rst x rc rf
  · intro i hi; rw [hro, hroc]; exact h.tab i ((hX i).not.mp hi)
  · intro i hi; rw [hroc]; exact h.nohit i ((hX i).mp hi)
  · intro y r; rw [hrf, hinp, hro]; exact h.comp y r
  · intro x tSF Z cf; rw [hsrv, hro, hrs]; exact h.srvI x tSF Z cf

omit [Fintype S] [Nonempty S] [DecidableEq Sec] [Fintype Sec] [Nonempty Sec] [Inhabited Sec] in
/-- The coupling holds with the stored output of the simulator cleared. -/
theorem cpl_reset {s : TRSt S W Tr VK SK Sec} {t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)}
    (h : Cpl A s t) : Cpl A s ((t.1.1, t.1.2.1, none), t.2) :=
  cpl_frame A h rfl h.com h.fcor rfl rfl rfl rfl rfl rfl rfl

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- The components of `comm`. -/
theorem comm_eq {s c : TRSt S W Tr VK SK Sec} (h : comm s = comm c) :
    s.lt = c.lt ∧ s.eph = c.eph ∧ s.srv = c.srv ∧ s.log = c.log ∧ s.st.corrupt = c.st.corrupt ∧
      s.st.notices = c.st.notices ∧ s.st.cursor = c.st.cursor := by
  simpa only [comm, Prod.mk.injEq] using h

/-- The oracle of the simulated game at an event that the simulator answers on its copy. -/
theorem simO_adv (t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) (e : TEv W Tr Sig Sec)
    (he : simCore A t.1 (.inr e) = (realAdvK lazyKDF A true t.1.1 e).map fun p =>
      ((p.2, t.1.2.1, none), .inr p.1)) :
    simO A t (.inr e) = (realAdvK lazyKDF A true t.1.1 e).map fun p =>
      (.inr p.1, ((p.2, t.1.2.1, none), t.2)) := by
  rw [simO_core, he, PMF.bind_map, ← PMF.bind_pure_comp]
  rfl

/-- A coupling of the steps of the filtered world and of the copy gives a coupling of the two
worlds at an event that the simulator answers on its copy. -/
theorem coupled_adv (s : TRSt S W Tr VK SK Sec)
    (t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) (e : TEv W Tr Sig Sec)
    (he : simCore A t.1 (.inr e) = (realAdvK lazyKDF A true t.1.1 e).map fun p =>
      ((p.2, t.1.2.1, none), .inr p.1))
    (h : Coupled (realAdvK lazyKDF A true s e) (realAdvK lazyKDF A true t.1.1 e) fun p q =>
      KeyHit A ((q.2, t.1.2.1, none), t.2) ∨
        (p.1 = q.1 ∧ Cpl A p.2 ((q.2, t.1.2.1, none), t.2))) :
    Coupled ((filtGameK lazyKDF A).oracle () s (.inr e)) (simO A t (.inr e))
      fun z₁ z₂ => KeyHit A z₂.2 ∨ (z₁.1 = z₂.1 ∧ Cpl A z₁.2 z₂.2) := by
  rw [simO_adv A t e he]
  refine coupled_map _ _ (h.mono ?_)
  rintro p q (hk | ⟨h1, h2⟩)
  · exact Or.inl hk
  · exact Or.inr ⟨by simp only [h1], h2⟩

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- The step of `poll`. -/
theorem pollStep_eq {K : Type} (st : St K) :
    pollStep st = ({ st with cursor := if (st.notices[st.cursor]?).isSome then st.cursor + 1
      else st.cursor }, st.notices[st.cursor]?) := by
  unfold pollStep
  split <;> simp_all

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- The signing key pair at its first use, as the image of a draw. -/
theorem ltAt_eq {T : Type} (s : TRStT S W Tr VK SK Sec T) (pid : PartyId) :
    ltAt A s pid = (match s.lt pid with
      | some l => PMF.pure l
      | none => A.sig.keyDist).map fun l => (l, { s with lt := Function.update s.lt pid (some l) })
    := by
  unfold ltAt
  cases hl : s.lt pid with
  | none => rfl
  | some l =>
    simp only [PMF.pure_map]
    congr
    rw [← hl, Function.update_eq_self]

/-- The step of `idle`, `poll`, `pub`, `hello` from coupled states. -/
theorem coupled_simple (s : TRSt S W Tr VK SK Sec)
    (t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) (h : Cpl A s t) (e : TEv W Tr Sig Sec)
    (he : e = .idle ∨ e = .poll ∨ (∃ pid, e = .pub pid) ∨ ∃ sid pid, e = .hello sid pid) :
    Coupled ((filtGameK lazyKDF A).oracle () s (.inr e)) (simO A t (.inr e))
      fun z₁ z₂ => KeyHit A z₂.2 ∨ (z₁.1 = z₂.1 ∧ Cpl A z₁.2 z₂.2) := by
  obtain ⟨hlt, heph, hsrv, hlog, hcor, hnot, hcur⟩ := comm_eq h.com
  rcases he with rfl | rfl | ⟨pid, rfl⟩ | ⟨sid, pid, rfl⟩
  · exact coupled_adv A s t _ rfl (coupled_pure (Or.inr ⟨rfl, cpl_reset A h⟩))
  · refine coupled_adv A s t _ rfl (coupled_pure (Or.inr ⟨?_, ?_⟩))
    · simp only [pollStep_eq, hnot, hcur]
    · refine cpl_frame A h rfl ?_ ?_ ?_ ?_ rfl rfl rfl rfl rfl
      · simp only [comm, pollStep_eq, hlt, heph, hsrv, hlog, hcor, hnot, hcur]
      · simp only [pollStep_eq, h.fcor]
      · simp only [pollStep_eq]
      · simp only [pollStep_eq]
  · refine coupled_adv A s t _ rfl ?_
    simp only [realAdvK, ltAt_eq, PMF.map_comp, hlt]
    refine coupled_map _ _ ((coupled_same _).mono ?_)
    rintro l _ rfl
    refine Or.inr ⟨rfl, cpl_frame A h rfl ?_ h.fcor rfl rfl rfl rfl rfl rfl rfl⟩
    simp only [comm, Function.comp_apply, heph, hsrv, hlog, hcor, hnot, hcur]
  · refine coupled_adv A s t _ rfl ?_
    have hr := h.rsc (sid, pid)
    have hid : Cpl A s ((t.1.1, t.1.2.1, none), t.2) := cpl_reset A h
    simp only [realAdvK, helloStep]
    rcases hs : s.st.recs (sid, pid) with _ | rs <;>
      rcases hc : t.1.1.st.recs (sid, pid) with _ | rc <;>
      simp only [hs, hc, Option.map_none, Option.map_some, reduceCtorEq] at hr ⊢
    · exact coupled_pure (Or.inr ⟨rfl, hid⟩)
    · have hrole : rs.role = rc.role := by
        simp only [shp, Option.some.injEq, Prod.mk.injEq] at hr
        exact hr.2.1
      rw [hrole, ← heph]
      split_ifs
      · cases he : s.eph (sid, pid) with
        | some xs => exact coupled_pure (Or.inr ⟨rfl, hid⟩)
        | none =>
          refine coupled_map _ _ ((coupled_same _).mono ?_)
          rintro xs _ rfl
          refine Or.inr ⟨rfl, cpl_frame A h rfl ?_ h.fcor rfl rfl rfl rfl rfl rfl rfl⟩
          simp only [comm, heph, hlt, hsrv, hlog, hcor, hnot, hcur]
      · exact coupled_pure (Or.inr ⟨rfl, hid⟩)

/-- The step of `kdf` from coupled states: a query at an external input of a session whose key
the functionality chose is a query at the key of a fresh session; any other query receives the
same answer in both worlds. -/
theorem coupled_kdf (s : TRSt S W Tr VK SK Sec)
    (t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) (h : Cpl A s t) (z : TInp Tr W) :
    Coupled ((filtGameK lazyKDF A).oracle () s (.inr (.kdf z))) (simO A t (.inr (.kdf z)))
      fun z₁ z₂ => KeyHit A z₂.2 ∨ (z₁.1 = z₂.1 ∧ Cpl A z₁.2 z₂.2) := by
  refine coupled_adv A s t _ rfl ?_
  simp only [realAdvK, lazyKDF, roAt_eq_roDet, PMF.map_comp]
  refine coupled_map _ _ ((coupled_same _).mono ?_)
  rintro k _ rfl
  by_cases hX : XIn A t z
  · refine Or.inl (keyHit_of A (t := ((_, t.1.2.1, none), t.2)) hX ?_)
    simp [roDet_lookup]
  · obtain ⟨h1, h2⟩ := cpl_roDet A h hX k
    exact Or.inr ⟨by simp only [Function.comp_apply, h1], cpl_reset A h2⟩

/-- The oracle of the simulated game at an event of the honest port. -/
theorem simO_hon (t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) (e : HEv) :
    simO A t (.inl e) = (realHonK lazyKDF t.1.1 e).map fun p =>
      (.inl (honStep t.2 e).2, ((p.2, t.1.2.1, none), (honStep t.2 e).1)) := by
  rw [simO_core]
  simp only [simCore, PMF.bind_map]
  rw [← PMF.bind_pure_comp]
  congr 1
  funext p
  simp only [Function.comp_apply, fStepD, fwdOut, simReset]
  exact PMF.map_const _ _

omit [Fintype S] [Nonempty S] [DecidableEq Sec] [Fintype Sec] [Nonempty Sec] [Inhabited Sec] in
/-- The keys of coupled states agree with the keys of the functionality. -/
theorem keyOf_eq {s : TRSt S W Tr VK SK Sec} {t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)}
    (h : Cpl A s t) (x : Inst) : keyOf s.st x = keyOf t.2 x := by
  have hx := h.rsf x
  unfold keyOf
  cases h1 : s.st.recs x <;> cases h2 : t.2.recs x <;> simp_all [shk]

omit [Fintype S] [Nonempty S] [DecidableEq Sec] [Fintype Sec] [Nonempty Sec] [Inhabited Sec] in
/-- A new session at an instance without record keeps the coupling. -/
theorem cpl_addSession {s : TRSt S W Tr VK SK Sec}
    {t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)} (h : Cpl A s t) (x : Inst)
    (peer : PartyId) (role : Role) (hx : s.st.recs x = none) :
    Cpl A { s with st := addSession s.st x peer role }
      (({ t.1.1 with st := addSession t.1.1.st x peer role }, t.1.2.1, none),
        addSession t.2 x peer role) := by
  obtain ⟨hlt, heph, hsrv, hlog, hcor, hnot, hcur⟩ := comm_eq h.com
  have hc : t.1.1.st.recs x = none := by
    have := h.rsc x; rw [hx] at this; cases h' : t.1.1.st.recs x <;> simp_all
  have hf : t.2.recs x = none := by
    have := h.rsf x; rw [hx] at this; cases h' : t.2.recs x <;> simp_all
  have hX : ∀ i, XIn A (({ t.1.1 with st := addSession t.1.1.st x peer role }, t.1.2.1, none),
      addSession t.2 x peer role) i ↔ XIn A t i := by
    intro i
    simp only [XIn, addSession, hf, Option.isSome_none, Bool.false_eq_true, ite_false]
    constructor
    · rintro ⟨y, r, ip, h1, h2, h3, h4⟩
      by_cases hy : y = x
      · subst hy
        simp only [Function.update_self, Option.some.injEq] at h1
        subst h1
        simp at h2
      · rw [Function.update_of_ne hy] at h1; exact ⟨y, r, ip, h1, h2, h3, h4⟩
    · rintro ⟨y, r, ip, h1, h2, h3, h4⟩
      have hy : y ≠ x := by rintro rfl; rw [hf] at h1; cases h1
      exact ⟨y, r, ip, by rw [Function.update_of_ne hy]; exact h1, h2, h3, h4⟩
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [comm, addSession, hx, hc, Option.isSome_none, Bool.false_eq_true, ite_false, hlt,
      heph, hsrv, hlog, hcor, hnot, hcur]
  · simp only [addSession, hc, hf, Option.isSome_none, Bool.false_eq_true, ite_false, h.fcor]
  · intro y
    simp only [addSession, hx, hc, Option.isSome_none, Bool.false_eq_true, ite_false]
    by_cases hy : y = x
    · subst hy; simp
    · simp only [Function.update_of_ne hy]; exact h.rsc y
  · intro y
    simp only [addSession, hx, hf, Option.isSome_none, Bool.false_eq_true, ite_false]
    by_cases hy : y = x
    · subst hy; simp
    · simp only [Function.update_of_ne hy]; exact h.rsf y
  · intro y rc rf
    simp only [addSession, hc, hf, Option.isSome_none, Bool.false_eq_true, ite_false]
    by_cases hy : y = x
    · subst hy; simp only [Function.update_self, Option.some.injEq]; rintro rfl rfl; simp
    · simp only [Function.update_of_ne hy]; exact h.rst y rc rf
  · intro i hi; exact h.tab i ((hX i).not.mp hi)
  · intro i hi; exact h.nohit i ((hX i).mp hi)
  · intro y r
    simp only [addSession, hf, Option.isSome_none, Bool.false_eq_true, ite_false]
    by_cases hy : y = x
    · subst hy; simp only [Function.update_self, Option.some.injEq]; rintro rfl; simp
    · simp only [Function.update_of_ne hy]; exact h.comp y r
  · intro y tSF Z cf hy
    obtain ⟨h1, r, h2, h3, h4⟩ := h.srvI y tSF Z cf hy
    have hyx : y ≠ x := by rintro rfl; rw [hx] at h2; cases h2
    refine ⟨h1, r, ?_, h3, h4⟩
    simp only [addSession, hx, Option.isSome_none, Bool.false_eq_true, ite_false,
      Function.update_of_ne hyx, h2]

/-- The steps of the honest port from coupled states. -/
theorem coupled_hon (s : TRSt S W Tr VK SK Sec)
    (t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) (h : Cpl A s t) (e : HEv) :
    Coupled ((filtGameK lazyKDF A).oracle () s (.inl e)) (simO A t (.inl e))
      fun z₁ z₂ => KeyHit A z₂.2 ∨ (z₁.1 = z₂.1 ∧ Cpl A z₁.2 z₂.2) := by
  rw [simO_hon]
  change Coupled ((realHonK lazyKDF s e).map fun p =>
    ((Sum.inl p.1 : TOOut W VK SK Sig Sec), p.2)) _ _
  refine coupled_map _ _ ?_
  rcases e with ⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩
  · have hr := h.rsc (sid, pid)
    have hf := h.rsf (sid, pid)
    simp only [realHonK, lazyKDF, PMF.pure_map, honStep]
    cases hs : s.st.recs (sid, pid) with
    | none =>
      have hc : t.1.1.st.recs (sid, pid) = none := by
        rw [hs] at hr; cases h' : t.1.1.st.recs (sid, pid) <;> simp_all
      simp only [hc, Option.isNone_none, ite_true]
      exact coupled_pure (Or.inr ⟨rfl, cpl_addSession A h _ peer role hs⟩)
    | some rs =>
      obtain ⟨rc, hc⟩ : ∃ rc, t.1.1.st.recs (sid, pid) = some rc := by
        rw [hs] at hr; cases h' : t.1.1.st.recs (sid, pid) <;> simp_all
      obtain ⟨rf, hf'⟩ : ∃ rf, t.2.recs (sid, pid) = some rf := by
        rw [hs] at hf; cases h' : t.2.recs (sid, pid) <;> simp_all
      have hadd : addSession t.2 (sid, pid) peer role = t.2 := by simp [addSession, hf']
      simp only [hc, Option.isNone_some, Bool.false_eq_true, ite_false, hadd]
      exact coupled_pure (Or.inr ⟨rfl, cpl_reset A h⟩)
  · simp only [realHonK, honStep]
    exact coupled_pure (Or.inr ⟨by rw [keyOf_eq A h], cpl_reset A h⟩)

/-- The oracle of the simulated game at `corrupt`. -/
theorem simO_corrupt (t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) (pid : PartyId) :
    simO A t (.inr (.corrupt pid)) = if Pending t.1.1 pid then
      PMF.pure (.inr .ack, ((t.1.1, t.1.2.1, none), t.2)) else
      (ltAt A t.1.1 pid).map fun l => (.inr (.secret l.1.2),
        (({ l.2 with st := corruptStep l.2.st pid }, t.1.2.1, none), corruptStep t.2 pid)) := by
  rw [simO_core]
  simp only [simCore]
  split_ifs with hp
  · rw [PMF.pure_bind]
  · simp only [corruptK, hp, Bool.false_eq_true, ite_false, PMF.map_comp, PMF.bind_map]
    rw [← PMF.bind_pure_comp]
    congr 1
    funext l
    simp only [Function.comp_apply, fStepD, fAdvD, fwdOut, simReset]
    exact PMF.map_const _ _

omit [Fintype S] [Nonempty S] [DecidableEq Sec] [Fintype Sec] [Nonempty Sec] [Inhabited Sec] in
/-- `Pending` agrees on coupled states. -/
theorem pending_eq {s : TRSt S W Tr VK SK Sec} {t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)}
    (h : Cpl A s t) (pid : PartyId) : Pending s pid = Pending t.1.1 pid := by
  obtain ⟨-, -, -, -, -, hnot, -⟩ := comm_eq h.com
  have hk : ∀ (u : TRSt S W Tr VK SK Sec) y,
      (keyOf u.st y).isNone = ((u.st.recs y).map shp).all fun q => !q.2.2 := by
    intro u y
    unfold keyOf
    rcases u.st.recs y with _ | ⟨_, _, _, _ | _⟩ <;> rfl
  have hP : ∀ (u : TRSt S W Tr VK SK Sec), Pending u pid = u.st.notices.any fun n =>
      match (u.st.recs (n.sid, n.pid)).map shp with
      | some q => q.2.2 && (n.pid == pid || q.1 == pid) &&
          ((u.st.recs (n.sid, q.1)).map shp).all fun q' => !q'.2.2
      | none => false := by
    intro u
    unfold Pending
    congr 1
    funext n
    rcases u.st.recs (n.sid, n.pid) with _ | r
    · rfl
    · simp only [hk]
      rfl
  rw [hP, hP, hnot]
  simp only [h.rsc]

/-- The step of `corrupt` from coupled states. -/
theorem coupled_corrupt (s : TRSt S W Tr VK SK Sec)
    (t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) (h : Cpl A s t) (pid : PartyId) :
    Coupled ((filtGameK lazyKDF A).oracle () s (.inr (.corrupt pid)))
      (simO A t (.inr (.corrupt pid)))
      fun z₁ z₂ => KeyHit A z₂.2 ∨ (z₁.1 = z₂.1 ∧ Cpl A z₁.2 z₂.2) := by
  obtain ⟨hlt, heph, hsrv, hlog, hcor, hnot, hcur⟩ := comm_eq h.com
  rw [simO_corrupt]
  change Coupled ((corruptK A s pid).map fun p =>
    ((Sum.inr p.1 : TOOut W VK SK Sig Sec), p.2)) _ _
  unfold corruptK
  rw [pending_eq A h]
  split_ifs
  · rw [PMF.pure_map]
    exact coupled_pure (Or.inr ⟨rfl, cpl_reset A h⟩)
  · simp only [ltAt_eq, PMF.map_comp, hlt]
    refine coupled_map _ _ ((coupled_same _).mono ?_)
    rintro l _ rfl
    refine Or.inr ⟨rfl, cpl_frame A h rfl ?_ ?_ rfl rfl ?_ rfl rfl rfl rfl⟩
    · simp only [comm, Function.comp_apply, corruptStep, heph, hsrv, hlog, hcor, hnot, hcur]
    · simp only [Function.comp_apply, corruptStep, h.fcor]
    · simp only [Function.comp_apply, corruptStep]

/-- The oracle of the simulated game at `srvRecv`. -/
theorem simO_srvRecv (t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) (x : Inst) (X : W) :
    simO A t (.inr (.srvRecv x.1 x.2 X)) = (srvRecvK lazyKDF A t.1.1 x X).map fun p =>
      (.inr p.1, ((if Impersonated A t.1.1 x X then
          { p.2 with st := impStepOf srvImp p.2.st x } else p.2, t.1.2.1, none),
        if Impersonated A t.1.1 x X then impStepOf srvImp t.2 x else t.2)) := by
  rw [simO_core]
  simp only [simCore, simSrvRecv, PMF.bind_map]
  rw [← PMF.bind_pure_comp]
  congr 1
  funext p
  simp only [Function.comp_apply]
  split_ifs
  · simp only [fStepD, fAdvD, fwdOut, simReset]
    exact PMF.map_const _ _
  · rfl

omit [Fintype S] [Nonempty S] [DecidableEq Sec] [Fintype Sec] [Nonempty Sec] [Inhabited Sec] in
/-- A record without key of a coupled state is not a session whose key the functionality
chose. -/
theorem not_completed_of_key {s : TRSt S W Tr VK SK Sec}
    {t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)} (h : Cpl A s t) {x : Inst}
    {r : Rec (TKey Sec)} (hr : t.2.recs x = some r) (hk : r.key = none) :
    r.status ≠ .completed := by
  intro hc
  obtain ⟨k, -, -, h1, -⟩ := h.comp x r hr hc
  rw [hk] at h1
  cases h1

omit [Fintype S] [Nonempty S] [DecidableEq Sec] [Fintype Sec] [Nonempty Sec] [Inhabited Sec] in
/-- `impersonate` at a responder session without key keeps the coupling. -/
theorem cpl_imp {s : TRSt S W Tr VK SK Sec} {t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)}
    (h : Cpl A s t) (x : Inst) (rs : Rec (TKey Sec)) (hs : s.st.recs x = some rs)
    (hk : rs.key = none) :
    Cpl A s ((({ t.1.1 with st := impStepOf srvImp t.1.1.st x }), t.1.2.1, none),
      impStepOf srvImp t.2 x) := by
  obtain ⟨hlt, heph, hsrv, hlog, hcor, hnot, hcur⟩ := comm_eq h.com
  have h1 := h.rsc x
  have h2 := h.rsf x
  rw [hs] at h1 h2
  obtain ⟨rc, hc⟩ : ∃ rc, t.1.1.st.recs x = some rc := by
    cases h' : t.1.1.st.recs x <;> simp_all
  obtain ⟨rf, hf⟩ : ∃ rf, t.2.recs x = some rf := by
    cases h' : t.2.recs x <;> simp_all
  rw [hc] at h1
  rw [hf] at h2
  simp only [Option.map_some, Option.some.injEq, shp, shk, Prod.mk.injEq] at h1 h2
  have hkf : rf.key = none := by rw [← h2.2.2, hk]
  have hkc : rc.key = none := by
    cases h' : rc.key <;> simp_all
  have hst : rc.status = rf.status := h.rst x rc rf hc hf hkf
  have hrole : rc.role = rf.role := by rw [← h1.2.1, h2.2.1]
  have hnc : rf.status ≠ .completed := not_completed_of_key A h hf hkf
  have eqc : impStepOf srvImp t.1.1.st x = if srvImp rc = true ∧ rc.status = .fresh then
      setRec t.1.1.st x { rc with status := .compromised } else t.1.1.st := by
    simp only [impStepOf, impStep, hc, hkc, Option.isNone_none, and_true]
    split_ifs <;> simp_all
  have eqf : impStepOf srvImp t.2 x = if srvImp rc = true ∧ rc.status = .fresh then
      setRec t.2 x { rf with status := .compromised } else t.2 := by
    simp only [impStepOf, impStep, hf, hkf, Option.isNone_none, and_true, srvImp, hrole, hst]
    split_ifs <;> simp_all [srvImp]
  rw [eqc, eqf]
  split_ifs with hP
  swap
  · exact cpl_reset A h
  have hX : ∀ i, XIn A ((({ t.1.1 with
      st := setRec t.1.1.st x { rc with status := .compromised } }), t.1.2.1, none),
      setRec t.2 x { rf with status := .compromised }) i ↔ XIn A t i := by
    intro i
    simp only [XIn, setRec]
    constructor
    · rintro ⟨y, r, ip, h1, h2, h3, h4⟩
      by_cases hy : y = x
      · subst hy
        simp only [Function.update_self, Option.some.injEq] at h1
        subst h1
        simp at h2
      · rw [Function.update_of_ne hy] at h1; exact ⟨y, r, ip, h1, h2, h3, h4⟩
    · rintro ⟨y, r, ip, h1, h2, h3, h4⟩
      have hy : y ≠ x := by rintro rfl; rw [hf] at h1; cases h1; exact hnc h2
      exact ⟨y, r, ip, by rw [Function.update_of_ne hy]; exact h1, h2, h3, h4⟩
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [comm, setRec, hlt, heph, hsrv, hlog, hcor, hnot, hcur]
  · simp only [setRec, h.fcor]
  · intro y
    simp only [setRec]
    by_cases hy : y = x
    · subst hy; simp [hs, shp, h1]
    · simp only [Function.update_of_ne hy]; exact h.rsc y
  · intro y
    simp only [setRec]
    by_cases hy : y = x
    · subst hy; simp [hs, shk, h2]
    · simp only [Function.update_of_ne hy]; exact h.rsf y
  · intro y rc' rf'
    simp only [setRec]
    by_cases hy : y = x
    · subst hy; simp only [Function.update_self, Option.some.injEq]; rintro rfl rfl _; rfl
    · simp only [Function.update_of_ne hy]; exact h.rst y rc' rf'
  · intro i hi; exact h.tab i ((hX i).not.mp hi)
  · intro i hi; exact h.nohit i ((hX i).mp hi)
  · intro y r
    simp only [setRec]
    by_cases hy : y = x
    · subst hy; simp only [Function.update_self, Option.some.injEq]; rintro rfl; simp
    · simp only [Function.update_of_ne hy]; exact h.comp y r
  · exact h.srvI

omit [Fintype S] [Nonempty S] [DecidableEq Sec] [Fintype Sec] [Nonempty Sec] [Inhabited Sec] in
/-- Recording the answer of a server session keeps the coupling. -/
theorem cpl_srv {s : TRSt S W Tr VK SK Sec} {t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)}
    (h : Cpl A s t) (x : Inst) (tSF : Tr) (Z : W) (cf : Sec) (L L' : List Tr) (hL : L = L')
    (r : Rec (TKey Sec))
    (hr : s.st.recs x = some r) (hrole : r.role = .responder) (htr : TrOf A x r.role r.peer tSF)
    (hcf : s.ro.lookup ⟨.cfin, tSF, Z⟩ = some cf) :
    Cpl A { s with srv := Function.update s.srv x (some (tSF, Z, cf)),
                   log := Function.update s.log x.2 L }
      (({ t.1.1 with srv := Function.update t.1.1.srv x (some (tSF, Z, cf)),
                     log := Function.update t.1.1.log x.2 L' }, t.1.2.1, t.1.2.2), t.2) := by
  obtain ⟨hlt, heph, hsrv, hlog, hcor, hnot, hcur⟩ := comm_eq h.com
  refine ⟨h.ph, ?_, h.fcor, h.rsc, h.rsf, h.rst, h.tab, h.nohit, h.comp, ?_⟩
  · simp only [comm, hlt, heph, hsrv, hlog, hcor, hnot, hcur, hL]
  · intro y tSF' Z' cf' hy
    by_cases hyx : y = x
    · subst hyx
      simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hy
      obtain ⟨rfl, rfl, rfl⟩ := hy
      exact ⟨hcf, r, hr, hrole, htr⟩
    · simp only [Function.update_of_ne hyx] at hy
      exact h.srvI y tSF' Z' cf' hy

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- Inputs with the labels `sfin` and `cfin` are not external stage inputs. -/
theorem not_xIn_of_lbl {t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)} {i : TInp Tr W}
    (hi : i.lbl = .sfin ∨ i.lbl = .cfin) : ¬ XIn A t i := by
  rintro ⟨y, r, ip, -, -, -, -, h⟩
  rcases h with ⟨h1 | h1 | h1, -⟩ | ⟨h1, -⟩ <;> rcases hi with hi | hi <;> rw [hi] at h1 <;>
    cases h1

/-- The step of `srvRecv` from coupled states. -/
theorem coupled_srvRecv (s : TRSt S W Tr VK SK Sec)
    (t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) (h : Cpl A s t) (sid : SessionId)
    (pid : PartyId) (X : W) :
    Coupled ((filtGameK lazyKDF A).oracle () s (.inr (.srvRecv sid pid X)))
      (simO A t (.inr (.srvRecv sid pid X)))
      fun z₁ z₂ => KeyHit A z₂.2 ∨ (z₁.1 = z₂.1 ∧ Cpl A z₁.2 z₂.2) := by
  obtain ⟨hlt, heph, hsrv, hlog, hcor, hnot, hcur⟩ := comm_eq h.com
  rw [simO_srvRecv A t (sid, pid) X]
  change Coupled ((srvRecvK lazyKDF A s (sid, pid) X).map fun p =>
    ((Sum.inr p.1 : TOOut W VK SK Sig Sec), p.2)) _ _
  have hr := h.rsc (sid, pid)
  unfold srvRecvK
  cases hs : s.st.recs (sid, pid) with
  | none =>
    have hc : t.1.1.st.recs (sid, pid) = none := by
      rw [hs] at hr; cases h' : t.1.1.st.recs (sid, pid) <;> simp_all
    have hi : Impersonated A t.1.1 (sid, pid) X = false := by simp [Impersonated, hc]
    simp only [hc, hi, PMF.pure_map, Bool.false_eq_true, ite_false]
    exact coupled_pure (Or.inr ⟨rfl, cpl_reset A h⟩)
  | some rs =>
    obtain ⟨rc, hc⟩ : ∃ rc, t.1.1.st.recs (sid, pid) = some rc := by
      rw [hs] at hr; cases h' : t.1.1.st.recs (sid, pid) <;> simp_all
    rw [hs, hc] at hr
    simp only [Option.map_some, Option.some.injEq, shp, Prod.mk.injEq] at hr
    obtain ⟨hpeer, hrole, hkey⟩ := hr
    have hkey' : rs.key.isNone = rc.key.isNone := by
      cases h1 : rs.key <;> cases h2 : rc.key <;> simp_all
    simp only [hc, ← hrole, ← hkey', ← hsrv, ← hpeer]
    by_cases hcond : rs.role = .responder ∧ rs.key.isNone = true ∧ (s.srv (sid, pid)).isNone = true
    swap
    · have hi : Impersonated A t.1.1 (sid, pid) X = false := by
        simp only [Impersonated, hc, decide_eq_false_iff_not, ← hrole, ← hkey', ← hsrv]
        exact fun h' => hcond ⟨h'.1, h'.2.1, h'.2.2.1⟩
      simp only [hcond, hi, PMF.pure_map, Bool.false_eq_true, ite_false]
      exact coupled_pure (Or.inr ⟨rfl, cpl_reset A h⟩)
    simp only [hcond, and_self, ite_true, PMF.map_bind, ltAt_eq, PMF.bind_map, hlt, lazyKDF,
      roAt_eq_roDet, PMF.map_comp]
    refine coupled_bind (coupled_same _) ?_
    rintro l _ rfl
    simp only [Function.comp_apply, PMF.map_bind, PMF.map_comp]
    refine coupled_bind (coupled_same _) ?_
    rintro y _ rfl
    refine coupled_bind (coupled_same _) ?_
    rintro σ _ rfl
    refine coupled_bind (coupled_same _) ?_
    rintro k₁ _ rfl
    refine coupled_map _ _ ((coupled_same _).mono ?_)
    rintro k₂ _ rfl
    simp only [Function.comp_apply]
    have h₁ : Cpl A { s with lt := Function.update t.1.1.lt pid (some l) }
        (({ t.1.1 with lt := Function.update t.1.1.lt pid (some l) }, t.1.2.1, none), t.2) :=
      cpl_frame A h rfl (by simp only [comm, heph, hsrv, hlog, hcor, hnot, hcur]) h.fcor
        rfl rfl rfl rfl rfl rfl rfl
    set tC := A.trCert (A.tr1 sid rs.peer pid X (A.pub y)) l.1
    set i₁ : TInp Tr W := ⟨.sfin, A.trCV tC σ, A.dh y X⟩
    obtain ⟨e1, h₂⟩ := cpl_roDet A h₁ (i := i₁) (not_xIn_of_lbl A (Or.inl rfl)) k₁
    set i₂ : TInp Tr W := ⟨.cfin, A.trSF (A.trCV tC σ) (roDet t.1.1.ro i₁ k₁).1, A.dh y X⟩
    obtain ⟨e2, h₃⟩ := cpl_roDet A h₂ (i := i₂) (not_xIn_of_lbl A (Or.inr rfl)) k₂
    dsimp only at e1 e2 h₂ h₃
    rw [e1]
    rw [e2]
    have htr : TrOf A (sid, pid) rs.role rs.peer
        (A.trSF (A.trCV tC σ) (roDet t.1.1.ro i₁ k₁).1) := by
      refine ⟨X, A.pub y, l.1, σ, (roDet t.1.1.ro i₁ k₁).1, ?_⟩
      simp only [hcond.1, reduceCtorEq, ite_false]
      grind
    have h₄ := cpl_srv A h₃ (sid, pid) (A.trSF (A.trCV tC σ) (roDet t.1.1.ro i₁ k₁).1) (A.dh y X)
      (roDet (roDet t.1.1.ro i₁ k₁).2 i₂ k₂).1 (tC :: s.log pid) (tC :: t.1.1.log pid)
      (by rw [hlog]) rs hs hcond.1 htr
      (by rw [roDet_lookup, ite_eq_left rfl, e2])
    refine Or.inr ⟨rfl, ?_⟩
    split_ifs
    · exact cpl_imp A h₄ (sid, pid) rs hs (Option.isNone_iff_eq_none.mp hcond.2.1)
    · exact h₄

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- External inputs stay external when the sessions whose key the functionality chose keep their
records and inputs. -/
theorem xIn_mono {t t' : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)}
    (h : ∀ y r, t.2.recs y = some r → r.status = .completed →
      t'.2.recs y = some r ∧ t'.1.2.1 y = t.1.2.1 y) {i : TInp Tr W} (hi : XIn A t i) :
    XIn A t' i := by
  obtain ⟨y, r, ip, h1, h2, h3, h4⟩ := hi
  obtain ⟨h5, h6⟩ := h y r h1 h2
  exact ⟨y, r, ip, h5, h2, by rw [h6, h3], h4⟩

omit [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Inhabited Sec] in
/-- A uniform key is four uniform stage values in sequence. -/
theorem uniform_tkey : PMF.uniformFintype (TKey Sec) =
    (PMF.uniformFintype Sec).bind fun a => (PMF.uniformFintype Sec).bind fun b =>
      (PMF.uniformFintype Sec).bind fun c =>
        (PMF.uniformFintype Sec).map fun d => (a, b, c, d) := by
  simp only [PMF.uniform_prod_eq_bind, PMF.map_bind, PMF.map_comp]
  rfl

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- **Two sessions on one transcript are partners**: with injective transcript operations, a
transcript of `x` and of `y ≠ x` names `y` as the peer of `x` in the protocol session of `x`,
with the other role. -/
theorem trOf_partner (hT : TrInj A.toTrOps) {x y : Inst} {rx ry : Role} {px py : PartyId}
    {tr : Tr} (hx : TrOf A x rx px tr) (hy : TrOf A y ry py tr) (hxy : x ≠ y) :
    y = (x.1, px) ∧ py = x.2 ∧ ry ≠ rx := by
  obtain ⟨X, Y, vk, σ, sf, rfl⟩ := hx
  obtain ⟨X', Y', vk', σ', sf', h⟩ := hy
  obtain ⟨h, -⟩ := hT.2.2.2.1 _ _ _ _ h
  obtain ⟨h, -⟩ := hT.2.2.1 _ _ _ _ h
  obtain ⟨h, -⟩ := hT.2.1 _ _ _ _ h
  obtain ⟨h1, h2, h3, -, -⟩ := hT.1 _ _ _ _ _ _ _ _ _ _ h
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  simp only at h1 h2 h3 ⊢
  subst h1
  cases rx <;> cases ry <;> simp_all

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- With injective transcript operations, an input external for two recorded inputs with the
label `cap` determines them. -/
theorem extIn_ext (hT : TrInj A.toTrOps) {ip ip' i : TInp Tr W} (hl : ip.lbl = .cap)
    (hl' : ip'.lbl = .cap) (h : ExtIn A ip i) (h' : ExtIn A ip' i) : ip = ip' := by
  obtain ⟨d, h⟩ := h
  obtain ⟨d', h'⟩ := h'
  have htr : ip.tr = ip'.tr := by
    rcases h with ⟨hl1, ht⟩ | ⟨hl1, cf, ht⟩ <;> rcases h' with ⟨hl2, ht'⟩ | ⟨hl2, cf', ht'⟩
    · rw [← ht, ← ht']
    · rcases hl1 with h1 | h1 | h1 <;> rw [h1] at hl2 <;> cases hl2
    · rcases hl2 with h1 | h1 | h1 <;> rw [h1] at hl1 <;> cases hl1
    · exact (hT.2.2.2.2 _ _ _ _ (ht.symm.trans ht')).1
  cases ip
  cases ip'
  simp_all

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- `setKey` at a session with a record. -/
theorem setKey_of {T : Type} {s : TRStT S W Tr VK SK Sec T} {x : Inst} {r : Rec (TKey Sec)}
    (h : s.st.recs x = some r) (k : TKey Sec) (ro : T) :
    setKey s x k ro = { s with st := setRec s.st x { r with key := some k }, ro := ro } := by
  simp [setKey, h]

omit [Fintype S] [Nonempty S] [DecidableEq Sec] [Fintype Sec] [Nonempty Sec] [Inhabited Sec] in
/-- The records of `x` in the three components of coupled states, for a session without key of
the filtered world. -/
theorem cpl_recs_of {s : TRSt S W Tr VK SK Sec}
    {t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)} (h : Cpl A s t) {x : Inst}
    {rs : Rec (TKey Sec)} (hs : s.st.recs x = some rs) (hk : rs.key = none) :
    ∃ rc rf, t.1.1.st.recs x = some rc ∧ t.2.recs x = some rf ∧ rc.peer = rs.peer ∧
      rc.role = rs.role ∧ rc.key = none ∧ rf.peer = rs.peer ∧ rf.role = rs.role ∧
      rf.key = none ∧ rc.status = rf.status ∧ rf.status ≠ .completed := by
  have h1 := h.rsc x
  have h2 := h.rsf x
  rw [hs] at h1 h2
  obtain ⟨rc, hc⟩ : ∃ rc, t.1.1.st.recs x = some rc := by
    cases h' : t.1.1.st.recs x <;> simp_all
  obtain ⟨rf, hf⟩ : ∃ rf, t.2.recs x = some rf := by
    cases h' : t.2.recs x <;> simp_all
  rw [hc] at h1
  rw [hf] at h2
  simp only [Option.map_some, Option.some.injEq, shp, shk, Prod.mk.injEq] at h1 h2
  have hkf : rf.key = none := by rw [← h2.2.2, hk]
  have hkc : rc.key = none := by cases h' : rc.key <;> simp_all
  exact ⟨rc, rf, hc, hf, h1.1.symm, h1.2.1.symm, hkc, h2.1.symm, h2.2.1.symm, hkf,
    h.rst x rc rf hc hf hkf, not_completed_of_key A h hf hkf⟩

omit [Fintype S] [Nonempty S] [DecidableEq Sec] [Fintype Sec] [Nonempty Sec] [Inhabited Sec] in
/-- **The completion of an exposed session keeps the coupling**: the key `K` in the three
components, the functionality marks the session compromised. -/
theorem cpl_exp {s : TRSt S W Tr VK SK Sec} {t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)}
    (h : Cpl A s t) {x : Inst} {rs rc rf : Rec (TKey Sec)} (hs : s.st.recs x = some rs)
    (hc : t.1.1.st.recs x = some rc) (hf : t.2.recs x = some rf) (hp : rc.peer = rs.peer)
    (hr : rc.role = rs.role) (hp' : rf.peer = rs.peer) (hr' : rf.role = rs.role)
    (hnc : rf.status ≠ .completed) (K : TKey Sec) (ip : TInp Tr W) :
    Cpl A { s with st := setRec s.st x { rs with key := some K } }
      (({ t.1.1 with st := setRec t.1.1.st x { rc with key := some K } },
        Function.update t.1.2.1 x (some ip), none),
        setRec t.2 x { rf with key := some K, status := .compromised }) := by
  obtain ⟨hlt, heph, hsrv, hlog, hcor, hnot, hcur⟩ := comm_eq h.com
  have hX : ∀ i, XIn A (({ t.1.1 with st := setRec t.1.1.st x { rc with key := some K } },
      Function.update t.1.2.1 x (some ip), none),
      setRec t.2 x { rf with key := some K, status := .compromised }) i ↔ XIn A t i := by
    intro i
    simp only [XIn, setRec]
    constructor
    · rintro ⟨y, r, ip', h1, h2, h3, h4⟩
      by_cases hy : y = x
      · subst hy
        simp only [Function.update_self, Option.some.injEq] at h1
        subst h1
        simp at h2
      · rw [Function.update_of_ne hy] at h1 h3; exact ⟨y, r, ip', h1, h2, h3, h4⟩
    · rintro ⟨y, r, ip', h1, h2, h3, h4⟩
      have hy : y ≠ x := by rintro rfl; rw [hf] at h1; cases h1; exact hnc h2
      exact ⟨y, r, ip', by rw [Function.update_of_ne hy]; exact h1, h2,
        by rw [Function.update_of_ne hy]; exact h3, h4⟩
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [comm, setRec, hlt, heph, hsrv, hlog, hcor, hnot, hcur]
  · simp only [setRec, h.fcor]
  · intro y
    simp only [setRec]
    by_cases hy : y = x
    · subst hy; simp [shp, hp, hr]
    · simp only [Function.update_of_ne hy]; exact h.rsc y
  · intro y
    simp only [setRec]
    by_cases hy : y = x
    · subst hy; simp [shk, hp', hr']
    · simp only [Function.update_of_ne hy]; exact h.rsf y
  · intro y rc' rf'
    simp only [setRec]
    by_cases hy : y = x
    · subst hy; simp only [Function.update_self, Option.some.injEq]; rintro rfl rfl hk; cases hk
    · simp only [Function.update_of_ne hy]; exact h.rst y rc' rf'
  · intro i hi; exact h.tab i ((hX i).not.mp hi)
  · intro i hi; exact h.nohit i ((hX i).mp hi)
  · intro y r
    simp only [setRec]
    by_cases hy : y = x
    · subst hy; simp only [Function.update_self, Option.some.injEq]; rintro rfl; simp
    · simp only [Function.update_of_ne hy]; exact h.comp y r
  · intro y tSF Z cf hy
    obtain ⟨h1, r, h2, h3, h4⟩ := h.srvI y tSF Z cf hy
    refine ⟨h1, ?_⟩
    simp only [setRec]
    by_cases hyx : y = x
    · subst hyx
      rw [hs] at h2; cases h2
      exact ⟨_, Function.update_self _ _ _, h3, h4⟩
    · exact ⟨r, by rw [Function.update_of_ne hyx]; exact h2, h3, h4⟩

omit [Fintype S] [Nonempty S] [DecidableEq Sec] [Fintype Sec] [Nonempty Sec] [Inhabited Sec] in
/-- **The completion of a session that receives the key of the functionality keeps the
coupling**: the filtered world has the key `K` at the stage inputs of the recorded input in its
table `T`, which extends its table by entries at inputs external for that input only; the copy's
table holds no input external for it. -/
theorem cpl_unexp {s : TRSt S W Tr VK SK Sec} {t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)}
    (h : Cpl A s t) {x : Inst} {rs rc rf : Rec (TKey Sec)} (hs : s.st.recs x = some rs)
    (hc : t.1.1.st.recs x = some rc) (hf : t.2.recs x = some rf) (hp : rc.peer = rs.peer)
    (hr : rc.role = rs.role) (hp' : rf.peer = rs.peer) (hr' : rf.role = rs.role)
    (K : TKey Sec) (tSF : Tr) (Z : W) (cf : Sec) (T : List (TInp Tr W × Sec))
    (htr : TrOf A x rs.role rs.peer tSF)
    (hK : T.lookup ⟨.cap, tSF, Z⟩ = some K.1 ∧ T.lookup ⟨.sap, tSF, Z⟩ = some K.2.1 ∧
      T.lookup ⟨.exp, tSF, Z⟩ = some K.2.2.1 ∧ T.lookup ⟨.cfin, tSF, Z⟩ = some cf ∧
      T.lookup ⟨.res, A.trCF tSF cf, Z⟩ = some K.2.2.2)
    (hext : ∀ j v, s.ro.lookup j = some v → T.lookup j = some v)
    (hsame : ∀ j, ¬ ExtIn A ⟨.cap, tSF, Z⟩ j → T.lookup j = s.ro.lookup j)
    (hno : ∀ j, ExtIn A ⟨.cap, tSF, Z⟩ j → t.1.1.ro.lookup j = none)
    (hnc : rf.status ≠ .completed) (kc : TKey Sec) :
    Cpl A { s with st := setRec s.st x { rs with key := some K }, ro := T }
      (({ t.1.1 with st := setRec t.1.1.st x { rc with key := some kc } },
        Function.update t.1.2.1 x (some ⟨.cap, tSF, Z⟩), none),
        setRec t.2 x { rf with key := some K, status := .completed }) := by
  obtain ⟨hlt, heph, hsrv, hlog, hcor, hnot, hcur⟩ := comm_eq h.com
  set ip : TInp Tr W := ⟨.cap, tSF, Z⟩ with hip
  set c' := { t.1.1 with st := setRec t.1.1.st x { rc with key := some kc } }
  set f' := setRec t.2 x { rf with key := some K, status := .completed } with hf'
  have hX : ∀ i, XIn A ((c', Function.update t.1.2.1 x (some ip), none), f') i ↔
      XIn A t i ∨ ExtIn A ip i := by
    intro i
    constructor
    · rintro ⟨y, r, ip', h1, h2, h3, h4⟩
      simp only [hf', setRec] at h1
      dsimp only at h3
      by_cases hy : y = x
      · subst hy; simp only [Function.update_self, Option.some.injEq] at h3; subst h3
        exact Or.inr h4
      · rw [Function.update_of_ne hy] at h1 h3; exact Or.inl ⟨y, r, ip', h1, h2, h3, h4⟩
    · rintro (⟨y, r, ip', h1, h2, h3, h4⟩ | h4)
      · have hy : y ≠ x := by rintro rfl; rw [hf] at h1; cases h1; exact hnc h2
        exact ⟨y, r, ip', by simp only [hf', setRec]; rw [Function.update_of_ne hy]; exact h1,
          h2, by dsimp only; rw [Function.update_of_ne hy]; exact h3, h4⟩
      · exact ⟨x, { rf with key := some K, status := .completed }, ip,
          by simp only [hf', setRec, Function.update_self], rfl,
          by dsimp only; exact Function.update_self _ _ _, h4⟩
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [c', comm, setRec, hlt, heph, hsrv, hlog, hcor, hnot, hcur]
  · simp only [c', hf', setRec, h.fcor]
  · intro y
    simp only [c', setRec]
    by_cases hy : y = x
    · subst hy; simp [shp, hp, hr]
    · simp only [Function.update_of_ne hy]; exact h.rsc y
  · intro y
    simp only [hf', setRec]
    by_cases hy : y = x
    · subst hy; simp [shk, hp', hr']
    · simp only [Function.update_of_ne hy]; exact h.rsf y
  · intro y rc' rf'
    simp only [c', hf', setRec]
    by_cases hy : y = x
    · subst hy; simp only [Function.update_self, Option.some.injEq]; rintro rfl rfl hk; cases hk
    · simp only [Function.update_of_ne hy]; exact h.rst y rc' rf'
  · intro i hi
    rw [hX] at hi
    push Not at hi
    rw [hsame i hi.2]
    exact h.tab i hi.1
  · intro i hi
    rcases (hX i).mp hi with hi | hi
    · exact h.nohit i hi
    · exact hno i hi
  · intro y r
    simp only [hf', setRec]
    by_cases hy : y = x
    · subst hy
      simp only [Function.update_self, Option.some.injEq]
      rintro rfl -
      exact ⟨K, ip, cf, rfl, rfl, rfl, by rw [hp', hr']; exact htr, hK⟩
    · simp only [Function.update_of_ne hy]
      intro hy1 hy2
      obtain ⟨k, ip', cf', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h.comp y r hy1 hy2
      exact ⟨k, ip', cf', h1, h2, h3, h4, hext _ _ h5, hext _ _ h6, hext _ _ h7, hext _ _ h8,
        hext _ _ h9⟩
  · intro y tSF' Z' cf' hy
    obtain ⟨h1, r, h2, h3, h4⟩ := h.srvI y tSF' Z' cf' hy
    refine ⟨hext _ _ h1, ?_⟩
    simp only [setRec]
    by_cases hyx : y = x
    · subst hyx
      rw [hs] at h2; cases h2
      exact ⟨_, Function.update_self _ _ _, h3, h4⟩
    · exact ⟨r, by rw [Function.update_of_ne hyx]; exact h2, h3, h4⟩

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- After a call of the random function its input is recorded. -/
theorem roDet_self_ne {D K : Type} [DecidableEq D] (T : List (D × K)) (i : D) (k : K) :
    (roDet T i k).2.lookup i ≠ none := by
  rw [roDet_lookup, ite_eq_left rfl]
  exact Option.some_ne_none _

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- A recorded input stays recorded. -/
theorem roDet_ne_of_ne {D K : Type} [DecidableEq D] (T : List (D × K)) (i j : D) (k : K)
    (h : T.lookup j ≠ none) : (roDet T i k).2.lookup j ≠ none := by
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp h
  rw [roDet_lookup_of_some _ _ _ _ hv]
  exact Option.some_ne_none _

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- A call of the random function at an input outside the table records the fresh value. -/
theorem roDet_of_none {D K : Type} [DecidableEq D] {T : List (D × K)} {i : D} (k : K)
    (h : T.lookup i = none) : roDet T i k = (k, (i, k) :: T) := by
  simp [roDet, h]

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- The lookup in a table extended at another input. -/
theorem lookup_cons_ne {D K : Type} [DecidableEq D] (T : List (D × K)) {i j : D} (k : K)
    (h : j ≠ i) : ((i, k) :: T).lookup j = T.lookup j := by
  simp only [List.lookup]
  grind

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- External inputs of coupled states stay external after the completion of a session without
key. -/
theorem xIn_complete {t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)} {x : Inst}
    {rf : Rec (TKey Sec)} (hf : t.2.recs x = some rf) (hnc : rf.status ≠ .completed)
    (c' : TRSt S W Tr VK SK Sec) (ip : TInp Tr W) (r' : Rec (TKey Sec)) {i : TInp Tr W}
    (hi : XIn A t i) : XIn A ((c', Function.update t.1.2.1 x (some ip), none), setRec t.2 x r') i :=
  xIn_mono A (fun y r hy hcomp => by
    have hyx : y ≠ x := by rintro rfl; rw [hf] at hy; cases hy; exact hnc hcomp
    exact ⟨by simp only [setRec]; rw [Function.update_of_ne hyx]; exact hy,
      by dsimp only; rw [Function.update_of_ne hyx]⟩) hi

omit [Fintype S] [Nonempty S] [DecidableEq Sec] [Inhabited Sec] in
/-- The key derivation of a session whose four stage inputs are in the table. -/
theorem keysK_of_some (T : List (TInp Tr W × Sec)) (x : Inst) (tSF : Tr) (Z : W) (cf : Sec)
    {K : TKey Sec} (h1 : T.lookup ⟨.cap, tSF, Z⟩ = some K.1)
    (h2 : T.lookup ⟨.sap, tSF, Z⟩ = some K.2.1) (h3 : T.lookup ⟨.exp, tSF, Z⟩ = some K.2.2.1)
    (h4 : T.lookup ⟨.res, A.trCF tSF cf, Z⟩ = some K.2.2.2) :
    keysK lazyKDF A T x tSF Z cf = PMF.pure (K, T) := by
  simp only [keysK, lazyKDF, CatCrypt.Crypto.PAKE.CPaceSquare.roAt, h1, h2, h3, h4,
    PMF.pure_bind, PMF.pure_map]

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- The four stage inputs of a session are external for its recorded input. -/
theorem extIn_stages (tSF : Tr) (Z : W) (cf : Sec) :
    ExtIn A ⟨.cap, tSF, Z⟩ ⟨.cap, tSF, Z⟩ ∧ ExtIn A ⟨.cap, tSF, Z⟩ ⟨.sap, tSF, Z⟩ ∧
      ExtIn A ⟨.cap, tSF, Z⟩ ⟨.exp, tSF, Z⟩ ∧ ExtIn A ⟨.cap, tSF, Z⟩ ⟨.res, A.trCF tSF cf, Z⟩ :=
  ⟨⟨rfl, Or.inl ⟨Or.inl rfl, rfl⟩⟩, ⟨rfl, Or.inl ⟨Or.inr (Or.inl rfl), rfl⟩⟩,
    ⟨rfl, Or.inl ⟨Or.inr (Or.inr rfl), rfl⟩⟩, ⟨rfl, Or.inr ⟨rfl, cf, rfl⟩⟩⟩

omit [Fintype S] [Nonempty S] [DecidableEq Sec] in
/-- **The completion of a session from coupled states.** The filtered world derives the key of
the session `x` at the transcript `tSF`, the value `Z` and the client Finished `cf`; the
simulated world delivers it through the functionality. -/
theorem coupled_complete (hT : TrInj A.toTrOps) (s : TRSt S W Tr VK SK Sec)
    (t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) (h : Cpl A s t) (x : Inst)
    (rs : Rec (TKey Sec)) (hs : s.st.recs x = some rs) (hk : rs.key = none) (tSF : Tr) (Z : W)
    (cf : Sec) (htr : TrOf A x rs.role rs.peer tSF)
    (hcf : s.ro.lookup ⟨.cfin, tSF, Z⟩ = some cf) (o : TOut W VK SK Sig Sec) :
    Coupled ((keysK lazyKDF A s.ro x tSF Z cf).map fun k =>
        ((Sum.inr o : TOOut W VK SK Sig Sec), setKey s x k.1 k.2))
      ((deliver A t.1.1 t.1.2.1 x tSF Z cf o).bind fun q => match q.2 with
        | .inl g => (PMF.uniformFintype (TKey Sec)).map fun kf =>
            (fwdOut .ack q.1.2.2 (fStepD t.2 g kf).2, (simReset q.1, (fStepD t.2 g kf).1))
        | .inr o => PMF.pure (.inr o, (q.1, t.2)))
      fun z₁ z₂ => KeyHit A z₂.2 ∨ (z₁.1 = z₂.1 ∧ Cpl A z₁.2 z₂.2) := by
  obtain ⟨rc, rf, hc, hf, hp, hr, hkc, hp', hr', hkf, hst, hnc⟩ := cpl_recs_of A h hs hk
  have hEE : Exposed t.1.1.st x rc ↔ Exposed t.2 x rf := by
    simp only [Exposed, h.fcor, hp, hp', hst]
  simp only [setKey_of hs, deliver, hc]
  by_cases hE : Exposed t.1.1.st x rc
  · have hsim : ∀ (k kf : TKey Sec), newKeyStep t.2 (x.1, x.2) k kf =
        setRec t.2 x { rf with key := some k, status := .compromised } := by
      intro k kf
      have hE' := hEE.mp hE
      simp only [Prod.mk.eta, X3DHSquareHops.newKeyStep_of hf hkf, newKeyVal, ite_eq_left hE']
    simp only [ite_eq_left hE, PMF.bind_map, Function.comp_def, fwdOut, simReset, fStepD,
      fAdvD, hsim, setKey_of hc]
    have hc' : ∀ {β : Type} (c : β), (PMF.uniformFintype (TKey Sec)).map (fun _ => c) =
        PMF.pure c := fun c => PMF.map_const _ c
    have hbp : ∀ {α β : Type} (p : PMF α) (f : α → β),
        p.bind (fun a => PMF.pure (f a)) = p.map f := fun p f => PMF.bind_pure_comp f p
    simp only [hc', hbp]
    simp only [keysK, lazyKDF, roAt_eq_roDet, PMF.map_bind, PMF.bind_map, PMF.map_comp,
      Function.comp_def]
    refine coupled_bind (coupled_same _) ?_
    rintro k₁ _ rfl
    refine coupled_bind (coupled_same _) ?_
    rintro k₂ _ rfl
    refine coupled_bind (coupled_same _) ?_
    rintro k₃ _ rfl
    refine coupled_map _ _ ((coupled_same _).mono ?_)
    rintro k₄ _ rfl
    set i₁ : TInp Tr W := ⟨.cap, tSF, Z⟩
    set i₂ : TInp Tr W := ⟨.sap, tSF, Z⟩
    set i₃ : TInp Tr W := ⟨.exp, tSF, Z⟩
    set i₄ : TInp Tr W := ⟨.res, A.trCF tSF cf, Z⟩
    have hX := fun (c' : TRSt S W Tr VK SK Sec) (K : TKey Sec) (i : TInp Tr W) (hi : XIn A t i) =>
      xIn_complete A hf hnc c' i₁ { rf with key := some K, status := .compromised } hi
    by_cases X1 : XIn A t i₁
    · exact Or.inl (keyHit_of A (hX _ _ _ X1) (roDet_ne_of_ne _ _ _ _ (roDet_ne_of_ne _ _ _ _
        (roDet_ne_of_ne _ _ _ _ (roDet_self_ne _ _ _)))))
    obtain ⟨e1, h1⟩ := cpl_roDet A h X1 k₁
    by_cases X2 : XIn A t i₂
    · exact Or.inl (keyHit_of A (hX _ _ _ X2) (roDet_ne_of_ne _ _ _ _ (roDet_ne_of_ne _ _ _ _
        (roDet_self_ne _ _ _))))
    obtain ⟨e2, h2⟩ := cpl_roDet A h1 X2 k₂
    by_cases X3 : XIn A t i₃
    · exact Or.inl (keyHit_of A (hX _ _ _ X3) (roDet_ne_of_ne _ _ _ _ (roDet_self_ne _ _ _)))
    obtain ⟨e3, h3⟩ := cpl_roDet A h2 X3 k₃
    by_cases X4 : XIn A t i₄
    · exact Or.inl (keyHit_of A (hX _ _ _ X4) (roDet_self_ne _ _ _))
    obtain ⟨e4, h4⟩ := cpl_roDet A h3 X4 k₄
    dsimp only at e1 e2 e3 e4
    rw [e1, e2, e3, e4]
    exact Or.inr ⟨rfl, cpl_exp A h4 hs hc hf hp hr hp' hr' hnc _ _⟩
  · have hE' : ¬ Exposed t.2 x rf := fun h' => hE (hEE.mpr h')
    set ip : TInp Tr W := ⟨.cap, tSF, Z⟩ with hip
    set L := (t.1.2.1 (x.1, rc.peer)).all (fun j => decide (j = ip)) with hL
    have hstep : ∀ kf, (fStepD t.2 (.inr (if L = true then AEv.newKey x.1 x.2 default
        else AEv.newKeyUnlinked x.1 x.2 default)) kf).1 = setRec t.2 x
          { rf with key := some (if L = true then newKeyVal t.2 x rf default kf else kf),
                    status := .completed } := by
      intro kf
      split_ifs <;> simp only [fStepD, fAdvD, Prod.mk.eta,
        X3DHSquareHops.newKeyStep_of hf hkf, X3DHSquareHops.newKeyFreshStep_of hf hkf,
        ite_eq_right hE']
    rw [ite_eq_right hE, PMF.pure_bind]
    simp only [fwdOut, simReset, setKey_of hc, hstep]
    by_cases U1 : ∃ y ry, t.2.recs y = some ry ∧ ry.status = .completed ∧ t.1.2.1 y = some ip
    · obtain ⟨y, ry, hy, hcomp, hinp⟩ := U1
      obtain ⟨ky, ipy, cfy, hky, hinpy, -, htry, l1, l2, l3, l4, l5⟩ := h.comp y ry hy hcomp
      rw [hinp, Option.some.injEq] at hinpy
      subst hinpy
      have hcfy : cfy = cf := by
        rw [hcf] at l4; exact (Option.some.injEq _ _ ▸ l4).symm
      subst hcfy
      have hyx : x ≠ y := by rintro rfl; rw [hf] at hy; cases hy; exact hnc hcomp
      obtain ⟨hyeq, hpy, hry⟩ := trOf_partner A hT htr htry hyx
      have hLt : L = true := by
        simp only [hL, hp, ← hyeq, hinp, Option.all_some, decide_true]
      have hV : ∀ kf, (if L = true then newKeyVal t.2 x rf default kf else kf) = ky := by
        intro kf
        have hpart : Partner x rf ry := ⟨hpy, by rw [hr']; exact hry, hcomp⟩
        simp only [hLt, ite_true, newKeyVal, ite_eq_right hE', hp', ← hyeq, hy, ite_eq_left hpart,
          hky,
          Option.getD_some]
      simp only [hV]
      rw [keysK_of_some A s.ro x tSF Z cfy l1 l2 l3 l5, PMF.pure_map,
        show ∀ {β : Type} (c : β), (PMF.uniformFintype (TKey Sec)).map (fun _ => c) =
          PMF.pure c from fun c => PMF.map_const _ c]
      refine coupled_pure (Or.inr ⟨rfl, ?_⟩)
      exact cpl_unexp A h hs hc hf hp hr hp' hr' ky tSF Z cfy s.ro htr ⟨l1, l2, l3, l4, l5⟩
        (fun _ _ hj => hj) (fun _ _ => rfl)
        (fun j hj => h.nohit j ⟨y, ry, ip, hy, hcomp, hinp, hj⟩) hnc default
    · push Not at U1
      have hnX : ∀ j, ExtIn A ip j → ¬ XIn A t j := by
        rintro j hj ⟨y, ry, ipy, hy, hcomp, hinp, hj'⟩
        obtain ⟨-, ipy', -, -, hinpy, hlbl, -⟩ := h.comp y ry hy hcomp
        rw [hinp, Option.some.injEq] at hinpy
        subst hinpy
        exact U1 y ry hy hcomp (by rw [hinp, extIn_ext A hT hlbl rfl hj' hj])
      have hV : ∀ kf, (if L = true then newKeyVal t.2 x rf default kf else kf) = kf := by
        intro kf
        split_ifs with hLt
        · simp only [newKeyVal, ite_eq_right hE']
          split
          · rename_i p hpr
            split_ifs with hpart
            · exfalso
              obtain ⟨-, ipp, -, -, hinpp, -⟩ := h.comp _ p hpr hpart.2.2
              have hpe : rc.peer = rf.peer := by rw [hp, hp']
              rw [hL, hpe, hinpp] at hLt
              simp only [Option.all_some, decide_eq_true_eq] at hLt
              exact U1 _ p hpr hpart.2.2 (by rw [hinpp, hLt])
            · rfl
          · rfl
        · rfl
      simp only [hV]
      by_cases U2a : ∃ j, ExtIn A ip j ∧ t.1.1.ro.lookup j ≠ none
      · obtain ⟨j, hj, hjl⟩ := U2a
        refine (coupled_indep _ _).mono ?_
        rintro a b ⟨-, hb⟩
        rw [PMF.mem_support_map_iff] at hb
        obtain ⟨kf, -, rfl⟩ := hb
        exact Or.inl (keyHit_of A ⟨x, { rf with key := some kf, status := .completed }, ip,
          by simp [setRec], rfl, Function.update_self _ _ _, hj⟩ hjl)
      push Not at U2a
      have hnone : ∀ j, ExtIn A ip j → s.ro.lookup j = none := fun j hj => by
        rw [h.tab j (hnX j hj)]; exact U2a j hj
      obtain ⟨E1, E2, E3, E4⟩ := extIn_stages A tSF Z cf
      set i₂ : TInp Tr W := ⟨.sap, tSF, Z⟩
      set i₃ : TInp Tr W := ⟨.exp, tSF, Z⟩
      set i₄ : TInp Tr W := ⟨.res, A.trCF tSF cf, Z⟩
      have n21 : i₂ ≠ ip := by simp [i₂, ip]
      have n31 : i₃ ≠ ip := by simp [i₃, ip]
      have n32 : i₃ ≠ i₂ := by simp [i₃, i₂]
      have n41 : i₄ ≠ ip := by simp [i₄, ip]
      have n42 : i₄ ≠ i₂ := by simp [i₄, i₂]
      have n43 : i₄ ≠ i₃ := by simp [i₄, i₃]
      have hn1 := hnone ip E1
      have hn2 := hnone i₂ E2
      have hn3 := hnone i₃ E3
      have hn4 := hnone i₄ E4
      rw [uniform_tkey]
      simp only [keysK, lazyKDF, roAt_eq_roDet, PMF.map_bind, PMF.bind_map, PMF.map_comp,
        Function.comp_def]
      refine coupled_bind (coupled_same _) ?_
      rintro k₁ _ rfl
      refine coupled_bind (coupled_same _) ?_
      rintro k₂ _ rfl
      refine coupled_bind (coupled_same _) ?_
      rintro k₃ _ rfl
      refine coupled_map _ _ ((coupled_same _).mono ?_)
      rintro k₄ _ rfl
      rw [roDet_of_none k₁ hn1]
      rw [roDet_of_none k₂ (by rw [lookup_cons_ne _ _ n21]; exact hn2)]
      rw [roDet_of_none k₃ (by rw [lookup_cons_ne _ _ n32, lookup_cons_ne _ _ n31]; exact hn3)]
      rw [roDet_of_none k₄ (by rw [lookup_cons_ne _ _ n43, lookup_cons_ne _ _ n42,
        lookup_cons_ne _ _ n41]; exact hn4)]
      dsimp only
      have hself : ∀ (T : List (TInp Tr W × Sec)) (i : TInp Tr W) (k : Sec),
          ((i, k) :: T).lookup i = some k := fun T i k => by simp [List.lookup]
      have hne : ∀ j, j ≠ ip → j ≠ i₂ → j ≠ i₃ → j ≠ i₄ →
          ((i₄, k₄) :: (i₃, k₃) :: (i₂, k₂) :: (ip, k₁) :: s.ro).lookup j = s.ro.lookup j :=
        fun j h1 h2 h3 h4 => by
          rw [lookup_cons_ne _ _ h4, lookup_cons_ne _ _ h3, lookup_cons_ne _ _ h2,
            lookup_cons_ne _ _ h1]
      have hcfin : ((i₄, k₄) :: (i₃, k₃) :: (i₂, k₂) :: (ip, k₁) :: s.ro).lookup
          ⟨.cfin, tSF, Z⟩ = some cf := by
        rw [hne _ (by simp [ip]) (by simp [i₂]) (by simp [i₃]) (by simp [i₄]), hcf]
      refine Or.inr ⟨rfl, cpl_unexp A h hs hc hf hp hr hp' hr' (k₁, k₂, k₃, k₄) tSF Z cf _ htr
        ⟨?_, ?_, ?_, hcfin, ?_⟩ ?_ ?_ U2a hnc default⟩
      · rw [lookup_cons_ne _ _ n41.symm, lookup_cons_ne _ _ n31.symm,
          lookup_cons_ne _ _ n21.symm, hself]
      · rw [lookup_cons_ne _ _ n42.symm, lookup_cons_ne _ _ n32.symm, hself]
      · rw [lookup_cons_ne _ _ n43.symm, hself]
      · exact hself _ _ _
      · intro j v hj
        rw [hne j (fun e => by rw [e, hn1] at hj; cases hj)
          (fun e => by rw [e, hn2] at hj; cases hj) (fun e => by rw [e, hn3] at hj; cases hj)
          (fun e => by rw [e, hn4] at hj; cases hj)]
        exact hj
      · intro j hj
        exact hne j (fun e => hj (e ▸ E1)) (fun e => hj (e ▸ E2)) (fun e => hj (e ▸ E3))
          (fun e => hj (e ▸ E4))

omit [Fintype S] [Nonempty S] [Inhabited Sec] in
/-- **The check of `cliRecv` from coupled states**: the same result, coupled states, and on
success a client session without key whose transcript and client Finished are recorded. -/
theorem coupled_cliCheck (s : TRSt S W Tr VK SK Sec)
    (t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) (h : Cpl A s t) (x : Inst) (Y : W)
    (σ : Sig) (sf : Sec) :
    Coupled (cliCheckK lazyKDF A true s x Y σ sf) (cliCheckK lazyKDF A true t.1.1 x Y σ sf)
      fun a b => a.1 = b.1 ∧ Cpl A a.2 ((b.2, t.1.2.1, none), t.2) ∧
        ∀ p, a.1 = some p → ∃ rs, a.2.st.recs x = some rs ∧ rs.key = none ∧
          TrOf A x rs.role rs.peer p.1 ∧ a.2.ro.lookup ⟨.cfin, p.1, p.2.1⟩ = some p.2.2 := by
  obtain ⟨hlt, heph, hsrv, hlog, hcor, hnot, hcur⟩ := comm_eq h.com
  have hid : Cpl A s ((t.1.1, t.1.2.1, none), t.2) := cpl_reset A h
  have hr := h.rsc x
  unfold cliCheckK
  rw [← heph]
  cases hs : s.st.recs x with
  | none =>
    have hc : t.1.1.st.recs x = none := by
      rw [hs] at hr; cases h' : t.1.1.st.recs x <;> simp_all
    simp only [hc]
    exact coupled_pure ⟨rfl, hid, fun p hp => by cases hp⟩
  | some rs =>
    obtain ⟨rc, hc⟩ : ∃ rc, t.1.1.st.recs x = some rc := by
      rw [hs] at hr; cases h' : t.1.1.st.recs x <;> simp_all
    rw [hs, hc] at hr
    simp only [Option.map_some, Option.some.injEq, shp, Prod.mk.injEq] at hr
    obtain ⟨hpeer, hrole, hkey⟩ := hr
    have hkey' : rs.key.isNone = rc.key.isNone := by
      cases h1 : rs.key <;> cases h2 : rc.key <;> simp_all
    simp only [hc]
    cases he : s.eph x with
    | none =>
      simp only
      exact coupled_pure ⟨rfl, hid, fun p hp => by cases hp⟩
    | some xs =>
      simp only [← hrole, ← hkey', ← hpeer]
      by_cases hcond : rs.role = .initiator ∧ rs.key.isNone = true
      swap
      · simp only [hcond, ite_false]
        exact coupled_pure ⟨rfl, hid, fun p hp => by cases hp⟩
      simp only [hcond, and_self, ite_true, ltAt_eq, PMF.bind_map, hlt, lazyKDF, roAt_eq_roDet,
        Function.comp_def]
      refine coupled_bind (coupled_same _) ?_
      rintro l _ rfl
      refine coupled_bind (coupled_same _) ?_
      rintro k₁ _ rfl
      have h₁ : Cpl A { s with lt := Function.update t.1.1.lt rs.peer (some l) }
          (({ t.1.1 with lt := Function.update t.1.1.lt rs.peer (some l) }, t.1.2.1, none),
            t.2) :=
        cpl_frame A h rfl (by simp only [comm, heph, hsrv, hlog, hcor, hnot, hcur]) h.fcor
          rfl rfl rfl rfl rfl rfl rfl
      set tC := A.trCert (A.tr1 x.1 x.2 rs.peer (A.pub xs) Y) l.1
      set i₁ : TInp Tr W := ⟨.sfin, A.trCV tC σ, A.dh xs Y⟩
      obtain ⟨e1, h₂⟩ := cpl_roDet A h₁ (i := i₁) (not_xIn_of_lbl A (Or.inl rfl)) k₁
      dsimp only at e1 h₂
      simp only [e1]
      split_ifs with hv1 hv2 hv2
      · simp only [PMF.map_comp]
        refine coupled_map _ _ ((coupled_same _).mono ?_)
        rintro k₂ _ rfl
        simp only [Function.comp_apply]
        set i₂ : TInp Tr W := ⟨.cfin, A.trSF (A.trCV tC σ) sf, A.dh xs Y⟩
        obtain ⟨e2, h₃⟩ := cpl_roDet A h₂ (i := i₂) (not_xIn_of_lbl A (Or.inr rfl)) k₂
        dsimp only at e2 h₃
        refine ⟨by rw [e2], h₃, ?_⟩
        rintro p hp
        simp only [Option.some.injEq] at hp
        subst hp
        refine ⟨rs, hs, Option.isNone_iff_eq_none.mp hcond.2, ?_, ?_⟩
        · refine ⟨A.pub xs, Y, l.1, σ, sf, ?_⟩
          simp only [hcond.1, ite_true]
          grind
        · exact (roDet_lookup _ _ _ _).trans (ite_eq_left rfl)
      · exact absurd (by rwa [hcor, hlog] at hv1) hv2
      · exact absurd (by rwa [← hcor, ← hlog] at hv2) hv1
      · exact coupled_pure ⟨rfl, h₂, fun p hp => by cases hp⟩

/-- The step of `cliRecv` from coupled states. -/
theorem coupled_cliRecv (hT : TrInj A.toTrOps) (s : TRSt S W Tr VK SK Sec)
    (t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) (h : Cpl A s t) (sid : SessionId)
    (pid : PartyId) (Y : W) (σ : Sig) (sf : Sec) :
    Coupled ((filtGameK lazyKDF A).oracle () s (.inr (.cliRecv sid pid Y σ sf)))
      (simO A t (.inr (.cliRecv sid pid Y σ sf)))
      fun z₁ z₂ => KeyHit A z₂.2 ∨ (z₁.1 = z₂.1 ∧ Cpl A z₁.2 z₂.2) := by
  rw [simO_core]
  change Coupled ((realAdvK lazyKDF A true s (.cliRecv sid pid Y σ sf)).map fun p =>
    ((Sum.inr p.1 : TOOut W VK SK Sig Sec), p.2)) _ _
  simp only [realAdvK, simCore, PMF.bind_bind, PMF.map_bind]
  refine coupled_bind (coupled_cliCheck A s t h (sid, pid) Y σ sf) ?_
  rintro a b ⟨hab, hcpl, hpre⟩
  cases ha : a.1 with
  | none =>
    rw [ha] at hab
    simp only [← hab, PMF.pure_map, PMF.pure_bind]
    exact coupled_pure (Or.inr ⟨rfl, hcpl⟩)
  | some p =>
    rw [ha] at hab
    obtain ⟨rs, hs, hk, htr, hcf⟩ := hpre p ha
    simp only [← hab, PMF.map_comp]
    exact coupled_complete A hT a.2 ((b.2, t.1.2.1, none), t.2) hcpl (sid, pid) rs hs hk p.1
      p.2.1 p.2.2 htr hcf (.cliFin (some p.2.2))

omit [Fintype S] [Nonempty S] [Fintype Sec] [Nonempty Sec] [Inhabited Sec] in
/-- `srvFinCheck` agrees on coupled states. -/
theorem srvFinCheck_eq {s : TRSt S W Tr VK SK Sec}
    {t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)} (h : Cpl A s t) (x : Inst) (cfin : Sec) :
    srvFinCheck s x cfin = srvFinCheck t.1.1 x cfin := by
  obtain ⟨-, -, hsrv, -, -, -, -⟩ := comm_eq h.com
  have hF : ∀ (u : TRSt S W Tr VK SK Sec), srvFinCheck u x cfin =
      match (u.st.recs x).map shp, u.srv x with
      | some q, some p => if q.2.1 = .responder ∧ q.2.2 = false ∧ cfin = p.2.2 then some p
          else none
      | _, _ => none := by
    intro u
    unfold srvFinCheck
    rcases u.st.recs x with _ | ⟨_, _, _, _ | _⟩ <;> rcases u.srv x with _ | _ <;>
      simp [shp]
  rw [hF, hF, h.rsc x, hsrv]

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [Fintype Sec] [Nonempty Sec]
  [Inhabited Sec] in
/-- A successful `srvFinCheck` names a server session without key that answered. -/
theorem srvFinCheck_some {s : TRSt S W Tr VK SK Sec} {x : Inst} {cfin : Sec}
    {p : Tr × W × Sec} (h : srvFinCheck s x cfin = some p) :
    ∃ r, s.st.recs x = some r ∧ r.key = none ∧ s.srv x = some p := by
  unfold srvFinCheck at h
  split at h
  · rename_i r q h1 h2
    split_ifs at h with hc
    cases h
    exact ⟨r, h1, Option.isNone_iff_eq_none.mp hc.2.1, h2⟩
  · cases h

/-- The step of `srvFin` from coupled states. -/
theorem coupled_srvFin (hT : TrInj A.toTrOps) (s : TRSt S W Tr VK SK Sec)
    (t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) (h : Cpl A s t) (sid : SessionId)
    (pid : PartyId) (cfin : Sec) :
    Coupled ((filtGameK lazyKDF A).oracle () s (.inr (.srvFin sid pid cfin)))
      (simO A t (.inr (.srvFin sid pid cfin)))
      fun z₁ z₂ => KeyHit A z₂.2 ∨ (z₁.1 = z₂.1 ∧ Cpl A z₁.2 z₂.2) := by
  rw [simO_core]
  change Coupled ((realAdvK lazyKDF A true s (.srvFin sid pid cfin)).map fun p =>
    ((Sum.inr p.1 : TOOut W VK SK Sig Sec), p.2)) _ _
  simp only [realAdvK, simCore, ← srvFinCheck_eq A h]
  cases hsf : srvFinCheck s (sid, pid) cfin with
  | none =>
    simp only [PMF.pure_map, PMF.pure_bind]
    exact coupled_pure (Or.inr ⟨rfl, cpl_reset A h⟩)
  | some p =>
    obtain ⟨r, hs, hk, hsrv⟩ := srvFinCheck_some hsf
    obtain ⟨hcf, r', hs', -, htr⟩ := h.srvI (sid, pid) p.1 p.2.1 p.2.2 hsrv
    rw [hs, Option.some.injEq] at hs'
    subst hs'
    simp only [PMF.map_comp]
    exact coupled_complete A hT s t h (sid, pid) r hs hk p.1 p.2.1 p.2.2 htr hcf .ack

/-- **A step of the two worlds from coupled states** is coupled so that the step of the
simulated world reaches a query at the key of a fresh session, or the answers agree and the
states stay coupled. -/
theorem step_coupled (hT : TrInj A.toTrOps) (s : TRSt S W Tr VK SK Sec)
    (t : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)) (e : TOEv W Tr Sig Sec) (h : Cpl A s t) :
    Coupled ((filtGameK lazyKDF A).oracle () s e) (simO A t e)
      fun z₁ z₂ => KeyHit A z₂.2 ∨ (z₁.1 = z₂.1 ∧ Cpl A z₁.2 z₂.2) := by
  rcases e with e | (_ | _ | pid | pid | ⟨sid, pid⟩ | ⟨sid, pid, X⟩ | ⟨sid, pid, Y, σ, sf⟩ |
    ⟨sid, pid, cfin⟩ | z)
  · exact coupled_hon A s t h e
  · exact coupled_simple A s t h _ (Or.inl rfl)
  · exact coupled_simple A s t h _ (Or.inr (Or.inl rfl))
  · exact coupled_simple A s t h _ (Or.inr (Or.inr (Or.inl ⟨pid, rfl⟩)))
  · exact coupled_corrupt A s t h pid
  · exact coupled_simple A s t h _ (Or.inr (Or.inr (Or.inr ⟨sid, pid, rfl⟩)))
  · exact coupled_srvRecv A s t h sid pid X
  · exact coupled_cliRecv A hT s t h sid pid Y σ sf
  · exact coupled_srvFin A hT s t h sid pid cfin
  · exact coupled_kdf A s t h z

end Rel

section Bounds

variable {S W Tr VK SK Sig Sec : Type} [Field S] [Fintype S] [SampleableType W]
  [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec] [Nonempty Sec] [Inhabited Sec]
  (G : DHGroup S W) (Sg : PSigScheme Tr VK SK Sig) (trs : TrOps Tr W VK Sig Sec)

/-- **The gap Diffie–Hellman reduction for the `i`-th ClientHello** of the oracle adversary `B`:
the challenge `X` in the share of that client session, the challenge `Y` rerandomised into every
server share that answers `X`, the decision oracle answering the comparisons of the
key-derivation table at the (EC)DHE values the reduction does not know; it outputs the DHE value
of the first table entry that the decision oracle accepts at a rerandomised server share. -/
noncomputable def tlsGdhRed (i : ℕ)
    (B : OracleAdv (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) Bool) : GapDH_Adversary W :=
  fun O X Y => liftPMF (tlsGdhOut G Sg trs i O X Y B)

/-- **The gap Diffie–Hellman bound** of an oracle adversary `B` with at most `n` queries: the sum
over the guessed client sessions of the advantages of the reductions. -/
noncomputable def tlsGdhBound (n : ℕ)
    (B : OracleAdv (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) Bool) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range n, GapDH_Advantage (gapDHDef G) (tlsGdhRed G Sg trs i B)

/-- **The collision bound** of an oracle adversary with at most `n` queries: each of at most `n`
client shares collides with one of at most `n` received server shares with probability
`1 / |S|`. -/
noncomputable def tlsCollBound (S : Type) [Fintype S] (n : ℕ) : ℝ≥0∞ :=
  (n * n : ℝ≥0∞) / Fintype.card S

/-- **The filtered and the simulated TLS game agree up to the bad event.** For transcript
operations that are injective, the advantage of every oracle adversary `B` between the filtered
game and the simulated game is at most the probability of `TBad` in the simulated world. -/
theorem filt_advantage_le_badGame (hT : TrInj trs)
    (B : OracleAdv (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) Bool) :
    KeyedGame.advantage (filtGameK lazyKDF (tlsDHAlg G Sg trs)) (simGame (tlsDHAlg G Sg trs)) B ≤
      badProb (tlsDHAlg G Sg trs) B := by
  classical
  have h := absDiff_le_of_coupled ((filtGameK lazyKDF (tlsDHAlg G Sg trs)).oracle ())
    (simO (tlsDHAlg G Sg trs)) (fun _ _ x => KeyHit (tlsDHAlg G Sg trs) x.2)
    (Cpl (tlsDHAlg G Sg trs))
    (fun s t e hst => step_coupled (tlsDHAlg G Sg trs) hT s t e hst) B _ _
    (cpl_init (tlsDHAlg G Sg trs))
  have hm := OracleAdv.run_flagWhen_mono (simO (tlsDHAlg G Sg trs))
    (fun _ _ x => KeyHit (tlsDHAlg G Sg trs) x.2) (TBad (tlsDHAlg G Sg trs))
    (fun _ _ _ hk => Or.inl hk) B (simInit (tlsDHAlg G Sg trs))
  have h₁ : (filtGameK lazyKDF (tlsDHAlg G Sg trs)).accept B =
      ((OracleAdv.run ((filtGameK lazyKDF (tlsDHAlg G Sg trs)).oracle ()) B
        (tInitK lazyKDF)).map Prod.fst) true := by
    unfold KeyedGame.accept
    erw [PMF.pure_bind]
    rfl
  have h₂ : (simGame (tlsDHAlg G Sg trs)).accept B =
      ((OracleAdv.run (simO (tlsDHAlg G Sg trs)) B
        (simInit (tlsDHAlg G Sg trs))).map Prod.fst) true := by
    unfold KeyedGame.accept
    erw [PMF.pure_bind]
    rfl
  unfold KeyedGame.advantage badProb
  rw [h₁, h₂]
  refine h.trans ?_
  convert hm using 4

/-- **The advantage of the reduction** as a probability over the challenge exponents. -/
theorem gapDH_advantage_tlsGdhRed (i : ℕ)
    (B : OracleAdv (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) Bool) :
    GapDH_Advantage (gapDHDef G) (tlsGdhRed G Sg trs i B) =
      ((PMF.uniformFintype S).bind fun x => (PMF.uniformFintype S).bind fun y =>
        (tlsGdhOut G Sg trs i (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) B).map
          fun c => decide (c = G.pub (x * y))) true := by
  unfold GapDH_Advantage
  rw [← prTrue_liftPMF _ Heap.empty]
  congr 1
  funext h
  unfold GapDH_Game
  have hk : (gapDHDef G).keygen =
      liftPMF ((PMF.uniformFintype S).map fun s => (G.pub s, G.pub s)) := rfl
  simp only [SPComp.monad_bind_eq, tlsGdhRed, hk]
  rw [liftPMF_bind_apply, PMF.bind_map]
  conv_rhs => unfold liftPMF
  rw [PMF.map_bind]
  refine congrArg _ (funext fun x => ?_)
  simp only [Function.comp_apply]
  rw [liftPMF_bind_apply, PMF.bind_map, PMF.map_bind]
  refine congrArg _ (funext fun y => ?_)
  simp only [Function.comp_apply]
  rw [liftPMF_bind_apply, PMF.map_comp, X3DHSquareGDH.cdh_pub]
  exact PMF.bind_pure_comp _ _

/-- **The extraction event** of the world of the reduction on `(g^x, g^y)`: the symbolic table
holds an entry with a known value `w` and the exponents hold a `v` with `w = (g^y · g^v)^x`. -/
def RGood (x y : S) (s : RW S W Tr VK SK Sec) : Prop :=
  ∃ p ∈ s.c.ro, ∃ w, p.1.dhe = .inl w ∧ ∃ v ∈ s.vs, w = G.exp (G.mul (G.pub y) (G.pub v)) x

omit [Fintype S] [SampleableType W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- The extraction event is kept by a larger table and more exponents. -/
theorem RGood.mono {x y : S} {s s' : RW S W Tr VK SK Sec} (h : RMono s s')
    (hg : RGood G x y s) : RGood G x y s' := by
  obtain ⟨p, hp, w, hw, v, hv, he⟩ := hg
  exact ⟨p, h.1 p hp, w, hw, v, h.2 v hv, he⟩

omit [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec] [Nonempty Sec] [Inhabited Sec] in
/-- **On the extraction event the reduction outputs the Diffie–Hellman value** `g^{xy}`. -/
theorem extractT_of_good {x y : S} {s : RW S W Tr VK SK Sec} (h : RGood G x y s) :
    extractT G (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) s = G.pub (x * y) := by
  obtain ⟨p, hp, w, hw, v, hv, he⟩ := h
  unfold extractT
  split
  · rename_i c hc
    obtain ⟨q, -, hq⟩ := List.mem_filterMap.mp (List.mem_of_mem_head? hc)
    split at hq
    · obtain ⟨v', hv', rfl⟩ := Option.map_eq_some_iff.mp hq
      have h1 := List.find?_some hv'
      rw [X3DHSquareGDH.ddhOracle_pub, decide_eq_true_eq] at h1
      rw [h1, G.mul_pub, G.exp_pub, G.exp_pub, G.mul_pub]
      congr 1
      ring
    · cases hq
  · rename_i hc
    rw [List.head?_eq_none_iff, List.filterMap_eq_nil_iff] at hc
    have h2 := hc p hp
    rw [hw] at h2
    simp only [Option.map_eq_none_iff, List.find?_eq_none] at h2
    have h3 := h2 v hv
    rw [X3DHSquareGDH.ddhOracle_pub, he] at h3
    simp at h3

/-- The value of a symbolic stage input at the secret `x` of the challenge share: a symbolic
value `inr E` is `E^x`. -/
def tinterp (x : S) (i : TInp Tr (W ⊕ W)) : TInp Tr W :=
  ⟨i.lbl, i.tr, X3DHSquareGDH.ev G x i.dhe⟩

/-- A symbolic table entry with its value at the secret `x`. -/
def tinterpE (x : S) (p : TInp Tr (W ⊕ W) × Sec) : TInp Tr W × Sec := (tinterp G x p.1, p.2)

/-- **Correctness of the symbolic equality of stage inputs** with the decision oracle of the
group. -/
theorem sinpEq_ddh (x : S) (i i' : TInp Tr (W ⊕ W)) :
    sinpEq G (ddhOracle (gapDHDef G)) (G.pub x) i i' = decide (tinterp G x i = tinterp G x i') := by
  simp only [sinpEq, X3DHSquareGDH.symEq_ddh, tinterp, TInp.mk.injEq, Bool.decide_and,
    Bool.and_assoc]

omit [DecidableEq Sec] [Fintype Sec] [Nonempty Sec] [Inhabited Sec] in
/-- **Correctness of the symbolic lookup**: the lookup of the values of the table. -/
theorem slook_ddh (x : S) (j : TInp Tr (W ⊕ W)) (tb : List (TInp Tr (W ⊕ W) × Sec)) :
    slook G (ddhOracle (gapDHDef G)) (G.pub x) j tb =
      (tb.map (tinterpE G x)).lookup (tinterp G x j) := by
  induction tb with
  | nil => rfl
  | cons p tb ih =>
    unfold slook at ih ⊢
    rw [List.find?_cons, List.map_cons, sinpEq_ddh]
    by_cases h : tinterp G x j = tinterp G x p.1
    · simp [h, tinterpE, List.lookup]
    · simp [h, tinterpE, List.lookup, ih]
      grind

omit [DecidableEq Sec] [Inhabited Sec] in
/-- **Correctness of the symbolic key derivation**: the lazily sampled random function on the
values of the table is the image of the symbolic one. -/
theorem roAt_tinterp (x : S) (tb : List (TInp Tr (W ⊕ W) × Sec)) (j : TInp Tr (W ⊕ W)) :
    CatCrypt.Crypto.PAKE.CPaceSquare.roAt (tb.map (tinterpE G x)) (tinterp G x j) =
      (sro G (ddhOracle (gapDHDef G)) (G.pub x) tb j).map
        fun p => (p.1, p.2.map (tinterpE G x)) := by
  unfold CatCrypt.Crypto.PAKE.CPaceSquare.roAt sro
  rw [← slook_ddh]
  cases slook G (ddhOracle (gapDHDef G)) (G.pub x) j tb with
  | some v => simp [PMF.pure_map]
  | none => simp [PMF.map_comp, Function.comp_def, tinterpE]

/-- **The coupling invariant of the world with the `j`-th client share fixed to `x` and the world
of the reduction** on `(g^x, g^y)`. The first world has no collision and no stored output; its
copy is the copy of the reduction with the symbolic values evaluated at `x` (a client secret
`none` is `x`); the inputs, the functionality, the number of shares and the `j`-th share agree.
In the world of the reduction: the functionality and the copy agree in corruption, record shapes
and the status of records without key, every record has a notice, a recorded input belongs to a
keyed session of its own transcript; a signed transcript and a server session that is not
compromised with the challenge share carry a rerandomised share `g^y · g^v`; a compromised record
of the copy is a server that received a share other than its client's; a compromised session of
the functionality is corrupt or compromised in the copy; a completed session whose partner has no
key has no corrupt party, its client drew a share, and its input carries `(g^y · g^v)^x` when that
share is the challenge; a symbolic external entry of the table belongs to a compromised session;
no completed and compromised sessions share a transcript; a server session of the copy that
answered has a responder record and a transcript of its own; and no record of the copy is
completed. -/
structure RCpl (x y : S) (j : ℕ) (s₁ : HSt S W Tr VK SK Sig Sec) (s₂ : RW S W Tr VK SK Sec) :
    Prop where
  /-- No collision. -/
  fl : s₁.1.2 = false
  /-- No stored output. -/
  ph : s₁.1.1.1.2.2 = none
  /-- The records, corrupt parties and notices of the copies agree. -/
  st : s₁.1.1.1.1.st = s₂.c.st
  /-- The signing keys agree. -/
  lt : s₁.1.1.1.1.lt = s₂.c.lt
  /-- The client secrets agree, `none` standing for `x`. -/
  eph : ∀ z, s₁.1.1.1.1.eph z = (s₂.c.eph z).map fun o => o.getD x
  /-- The server records agree at the values of the symbolic values. -/
  srv : ∀ z, s₁.1.1.1.1.srv z =
    (s₂.c.srv z).map fun p => (p.1, X3DHSquareGDH.ev G x p.2.1, p.2.2)
  /-- The signed transcripts agree. -/
  log : s₁.1.1.1.1.log = s₂.c.log
  /-- The table is the table of values of the symbolic table. -/
  ro : s₁.1.1.1.1.ro = s₂.c.ro.map (tinterpE G x)
  /-- The recorded inputs agree at their values. -/
  inp : ∀ z, s₁.1.1.1.2.1 z = (s₂.inp z).map (tinterp G x)
  /-- The functionalities agree. -/
  f : s₁.1.1.2 = s₂.f
  /-- The numbers of drawn client shares agree. -/
  cnt : s₁.2.1 = s₂.hellos
  /-- The `j`-th share is the challenge share. -/
  idx₁ : ∀ z, s₁.2.2 z = some j → s₂.c.eph z = some none
  /-- A drawn share has an index. -/
  idx₂ : ∀ z, (s₂.c.eph z).isSome → (s₁.2.2 z).isSome
  /-- The functionality and the copy have the same corrupt parties. -/
  fcor : s₂.f.corrupt = s₂.c.st.corrupt
  /-- The records of the functionality and of the copy have the same shape. -/
  rsh : ∀ z, (s₂.f.recs z).map shp = (s₂.c.st.recs z).map shp
  /-- A record without key has the same status in the copy and in the functionality. -/
  rst : ∀ z rc rf, s₂.c.st.recs z = some rc → s₂.f.recs z = some rf → rf.key = none →
    rc.status = rf.status
  /-- Every record of the copy has a notice. -/
  noticed : RecNoticed s₂.c.st
  /-- A recorded input belongs to a session with a key in the copy. -/
  inpKey : ∀ z ip, s₂.inp z = some ip → ∃ r, s₂.c.st.recs z = some r ∧ r.key.isSome
  /-- A signed transcript with the challenge share carries a rerandomised share. -/
  logY : ∀ pid t, t ∈ s₂.c.log pid → ∃ sid c sv X' Ys vk,
    t = trs.trCert (trs.tr1 sid c sv X' Ys) vk ∧
      (X' = G.pub x → ∃ v ∈ s₂.vs, Ys = G.mul (G.pub y) (G.pub v))
  /-- A server session that is not compromised received the share of its client, and its value
  is `(g^y · g^v)^x` for the challenge share. -/
  srvY : ∀ sv r tSF Z cf, s₂.c.st.recs sv = some r → s₂.c.srv sv = some (tSF, Z, cf) →
    r.status ≠ .compromised → ∃ o, s₂.c.eph (sv.1, r.peer) = some o ∧
      (o = none → ∃ v ∈ s₂.vs, Z = .inr (G.mul (G.pub y) (G.pub v)))
  /-- A compromised record of the copy is a server that received a share other than the share
  of its client. -/
  imp : ∀ z r, s₂.c.st.recs z = some r → r.status = .compromised → r.role = .responder ∧
    ∃ tSF Z cf, s₂.c.srv z = some (tSF, Z, cf) ∧ ∃ X' Ys vk σ sf,
      tSF = trs.trSF (trs.trCV (trs.trCert (trs.tr1 z.1 r.peer z.2 X' Ys) vk) σ) sf ∧
        shareR G (G.pub x) s₂ (z.1, r.peer) ≠ some X'
  /-- A compromised session of the functionality is corrupt or compromised in the copy. -/
  comp : ∀ z r, s₂.f.recs z = some r → r.status = .compromised →
    s₂.f.corrupt z.2 = true ∨ s₂.f.corrupt r.peer = true ∨
      ∃ rc, s₂.c.st.recs z = some rc ∧ rc.status = .compromised
  /-- A completed session whose partner has no key has no corrupt party. -/
  corr : ∀ z r, s₂.f.recs z = some r → r.status = .completed → keyOf s₂.f (z.1, r.peer) = none →
    s₂.f.corrupt z.2 = false ∧ s₂.f.corrupt r.peer = false
  /-- A recorded input has the label `cap` and a transcript of its session: the share of a
  client, the transcript of a server record. -/
  own : ∀ z ip, s₂.inp z = some ip → ip.lbl = .cap ∧ ∃ r, s₂.c.st.recs z = some r ∧
    ∃ X' Ys vk σ sf, ip.tr = trs.trSF (trs.trCV (trs.trCert (trs.tr1 z.1
      (if r.role = .initiator then z.2 else r.peer) (if r.role = .initiator then r.peer else z.2)
        X' Ys) vk) σ) sf ∧
      (r.role = .initiator → shareR G (G.pub x) s₂ z = some X') ∧
      (r.role = .responder → ∃ cf, s₂.c.srv z = some (ip.tr, ip.dhe, cf))
  /-- A completed session has its input, its client drew a share, and the input carries
  `(g^y · g^v)^x` for the challenge share. -/
  keyed : ∀ z r, s₂.f.recs z = some r → r.status = .completed → ∃ ip, s₂.inp z = some ip ∧
    ∃ o, s₂.c.eph (clientOf z r) = some o ∧
      (o = none → ∃ v ∈ s₂.vs, ip.dhe = .inr (G.mul (G.pub y) (G.pub v)))
  /-- A symbolic external entry of the table belongs to a compromised session. -/
  sym : ∀ p ∈ s₂.c.ro, ∀ E, p.1.dhe = .inr E →
    (p.1.lbl = .cap ∨ p.1.lbl = .sap ∨ p.1.lbl = .exp ∨ p.1.lbl = .res) →
    ∃ z r ip, s₂.f.recs z = some r ∧ r.status = .compromised ∧ s₂.inp z = some ip ∧
      ExtIn (tlsDHAlg G Sg trs) (tinterp G x ip) (tinterp G x p.1)
  /-- No completed and compromised sessions share a transcript. -/
  pair : ∀ z r z' r' ip ip', s₂.f.recs z = some r → r.status = .completed →
    s₂.f.recs z' = some r' → r'.status = .compromised → s₂.inp z = some ip →
    s₂.inp z' = some ip' → ip.tr ≠ ip'.tr
  /-- A server session that answered has a responder record and a transcript of its own. -/
  srvTr : ∀ z p, s₂.c.srv z = some p → ∃ r, s₂.c.st.recs z = some r ∧ r.role = .responder ∧
    ∃ X' Ys vk σ sf, p.1 = trs.trSF (trs.trCV (trs.trCert (trs.tr1 z.1 r.peer z.2 X' Ys) vk) σ) sf
  /-- No record of the copy is completed. -/
  ncomp : ∀ z r, s₂.c.st.recs z = some r → r.status ≠ .completed

/-- The initial states are related. -/
theorem rCpl_init (x y : S) (j : ℕ) :
    RCpl G Sg trs x y j (hInit (tlsDHAlg G Sg trs)) rwInit where
  fl := rfl
  ph := rfl
  st := rfl
  lt := rfl
  eph _ := rfl
  srv _ := rfl
  log := rfl
  ro := rfl
  inp _ := rfl
  f := rfl
  cnt := rfl
  idx₁ _ h := by simp [hInit] at h
  idx₂ _ h := by simp [rwInit] at h
  fcor := rfl
  rsh _ := rfl
  rst _ _ _ h := by simp [rwInit, initSt] at h
  noticed _ h := by simp [rwInit, initSt] at h
  inpKey _ _ h := by simp [rwInit] at h
  logY _ _ h := by simp [rwInit] at h
  srvY _ _ _ _ _ _ h := by simp [rwInit] at h
  imp _ _ h := by simp [rwInit, initSt] at h
  comp _ _ h := by simp [rwInit, initSt] at h
  corr _ _ h := by simp [rwInit, initSt] at h
  own _ _ h := by simp [rwInit] at h
  keyed _ _ h := by simp [rwInit, initSt] at h
  sym _ h := by simp [rwInit] at h
  pair _ _ _ _ _ _ h := by simp [rwInit, initSt] at h
  srvTr _ _ h := by simp [rwInit] at h
  ncomp _ _ h := by simp [rwInit, initSt] at h

omit [Fintype S] [SampleableType W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- **A query at the key of a fresh session of the `j`-th share is the extraction event**: from
related states, `KeyHitJ j` in the world with the `j`-th share fixed gives `RGood` in the world of
the reduction. -/
theorem rgood_of_keyHitJ (hT : TrInj trs) {x y : S} {j : ℕ} {s₁ : HSt S W Tr VK SK Sig Sec}
    {s₂ : RW S W Tr VK SK Sec} (h : RCpl G Sg trs x y j s₁ s₂)
    (hk : KeyHitJ (tlsDHAlg G Sg trs) j s₁) : RGood G x y s₂ := by
  obtain ⟨-, z, r, ip, i, k, hr, hc, hip, hik, hext, hj⟩ := hk
  rw [h.f] at hr
  obtain ⟨ip₂, hip₂, o, ho, hv⟩ := h.keyed z r hr hc
  rw [h.inp, hip₂, Option.map_some, Option.some.injEq] at hip
  subst hip
  have ho' : o = none := by
    rcases hj with hj | ⟨hj, -⟩
    · have h1 := h.idx₁ _ hj
      rw [ho, Option.some.injEq] at h1
      exact h1
    · have h1 := h.idx₂ (clientOf z r) (by rw [ho]; rfl)
      rw [hj] at h1
      cases h1
  obtain ⟨v, hvs, hdhe⟩ := hv ho'
  rw [h.ro, List.mem_map] at hik
  obtain ⟨p, hp, hpe⟩ := hik
  simp only [tinterpE, Prod.mk.injEq] at hpe
  obtain ⟨rfl, rfl⟩ := hpe
  rcases hd : p.1.dhe with w | E
  · refine ⟨p, hp, w, hd, v, hvs, ?_⟩
    have h1 := hext.1
    simp only [tinterp, hd, hdhe, X3DHSquareGDH.ev] at h1
    exact h1
  · exfalso
    have hl : p.1.lbl = .cap ∨ p.1.lbl = .sap ∨ p.1.lbl = .exp ∨ p.1.lbl = .res := by
      rcases hext.2 with ⟨hl, -⟩ | ⟨hl, -⟩
      · simp only [tinterp] at hl
        tauto
      · exact Or.inr (Or.inr (Or.inr hl))
    obtain ⟨z', r', ip', hr', hc', hip', hext'⟩ := h.sym p hp E hd hl
    have he := extIn_ext (tlsDHAlg G Sg trs) hT (h.own z ip₂ hip₂).1 (h.own z' ip' hip').1
      hext hext'
    have htr := congrArg TInp.tr he
    exact h.pair z r z' r' ip₂ ip' hr hc hr' hc' hip₂ hip' htr

/-- The step of `idle` from related states. -/
theorem red_idle (j : ℕ) (x y : S) (s₁ : HSt S W Tr VK SK Sig Sec) (s₂ : RW S W Tr VK SK Sec)
    (h : RCpl G Sg trs x y j s₁ s₂) :
    Coupled (hOx (tlsDHAlg G Sg trs) j x s₁ (.inr .idle))
      (redO G Sg trs j (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) s₂ (.inr .idle)) fun z₁ z₂ =>
        z₁.2.1.2 = true ∨ (z₁.1 = z₂.1 ∧ RCpl G Sg trs x y j z₁.2 z₂.2) := by
  obtain ⟨⟨⟨⟨c, inp, ph⟩, f⟩, fl⟩, cnt, idx⟩ := s₁
  have hph : ph = none := h.ph
  have hfl : fl = false := h.fl
  subst hph hfl
  have e1 : hOx (tlsDHAlg G Sg trs) j x ((((c, inp, none), f), false), cnt, idx) (.inr .idle) =
      PMF.pure (.inr .ack, ((((c, inp, none), f), false), cnt, idx)) := by
    simp [hOx, hO, collO, OracleAdv.flagWhen, simO_adv _ _ TEv.idle rfl, realAdvK, CollAt,
      idxStep, drawAt, PMF.pure_map]
  rw [e1]
  exact coupled_pure (Or.inr ⟨rfl, h⟩)

/-- The world with the indices at an event that the simulator answers on its copy, other than
`hello`. -/
theorem hO_adv (s₁ : HSt S W Tr VK SK Sig Sec) (e : TEv W Tr Sig Sec)
    (he : simCore (tlsDHAlg G Sg trs) s₁.1.1.1 (.inr e) =
      (realAdvK lazyKDF (tlsDHAlg G Sg trs) true s₁.1.1.1.1 e).map fun p =>
        ((p.2, s₁.1.1.1.2.1, none), .inr p.1))
    (hne : ∀ sid c, e ≠ .hello sid c)
    (hd : ∀ t t' : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec), drawAt t t' (.inr e) = none) :
    hO (tlsDHAlg G Sg trs) s₁ (.inr e) =
      (realAdvK lazyKDF (tlsDHAlg G Sg trs) true s₁.1.1.1.1 e).map fun p =>
        (.inr p.1, ((((p.2, s₁.1.1.1.2.1, none), s₁.1.1.2), s₁.1.2), s₁.2)) := by
  have hc : ∀ q, ¬ CollAt (tlsDHAlg G Sg trs) s₁.1.1 (.inr e) q := by
    rintro q ⟨sid, c, _, _, _, _, _, _, _, _, _, hh, -⟩
    exact hne sid c (Sum.inr.inj hh)
  simp only [hO, collO, OracleAdv.flagWhen, simO_adv _ _ e he, PMF.map_comp]
  congr 1
  funext p
  simp [hc, idxStep, hd]

/-- The step of `getKey` from related states. -/
theorem red_getKey (j : ℕ) (x y : S) (s₁ : HSt S W Tr VK SK Sig Sec) (s₂ : RW S W Tr VK SK Sec)
    (sid : SessionId) (pid : PartyId) (h : RCpl G Sg trs x y j s₁ s₂) :
    Coupled (hOx (tlsDHAlg G Sg trs) j x s₁ (.inl (.getKey sid pid)))
      (redO G Sg trs j (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) s₂
        (.inl (.getKey sid pid))) fun z₁ z₂ =>
        z₁.2.1.2 = true ∨ (z₁.1 = z₂.1 ∧ RCpl G Sg trs x y j z₁.2 z₂.2) := by
  obtain ⟨⟨⟨⟨c, inp, ph⟩, f⟩, fl⟩, cnt, idx⟩ := s₁
  have hph : ph = none := h.ph
  have hfl : fl = false := h.fl
  have hf : f = s₂.f := h.f
  subst hph hfl
  have e1 : hOx (tlsDHAlg G Sg trs) j x ((((c, inp, none), f), false), cnt, idx)
      (.inl (.getKey sid pid)) =
      PMF.pure (.inl (.key (keyOf f (sid, pid))), ((((c, inp, none), f), false), cnt, idx)) := by
    simp [hOx, hO, collO, OracleAdv.flagWhen, simO_hon, realHonK, honStep, CollAt,
      idxStep, drawAt, PMF.pure_map]
  rw [e1]
  exact coupled_pure (Or.inr ⟨by rw [hf], h⟩)

/-- The step of `pub` from related states. -/
theorem red_pub (j : ℕ) (x y : S) (s₁ : HSt S W Tr VK SK Sig Sec) (s₂ : RW S W Tr VK SK Sec)
    (pid : PartyId) (h : RCpl G Sg trs x y j s₁ s₂) :
    Coupled (hOx (tlsDHAlg G Sg trs) j x s₁ (.inr (.pub pid)))
      (redO G Sg trs j (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) s₂ (.inr (.pub pid)))
        fun z₁ z₂ => z₁.2.1.2 = true ∨ (z₁.1 = z₂.1 ∧ RCpl G Sg trs x y j z₁.2 z₂.2) := by
  obtain ⟨⟨⟨⟨c, inp, ph⟩, f⟩, fl⟩, cnt, idx⟩ := s₁
  have hph : ph = none := h.ph
  have hfl : fl = false := h.fl
  have hlt : c.lt = s₂.c.lt := h.lt
  subst hph hfl
  change Coupled (hO _ _ _) _ _
  rw [hO_adv G Sg trs _ _ rfl (fun _ _ h => by cases h) (fun _ _ => rfl)]
  simp only [realAdvK, ltAt_eq, PMF.map_comp, redO, rlt]
  rw [hlt]
  cases hl : s₂.c.lt pid with
  | some l =>
    simp only [PMF.pure_map]
    refine coupled_pure (Or.inr ⟨rfl, ?_⟩)
    have hu : Function.update s₂.c.lt pid (some l) = s₂.c.lt := by
      rw [← hl, Function.update_eq_self]
    exact { h with lt := by simp only [Function.comp_apply]; exact hu }
  | none =>
    simp only [PMF.map_comp]
    refine coupled_map _ _ ((coupled_same _).mono ?_)
    rintro l _ rfl
    exact Or.inr ⟨rfl, { h with lt := by simp only [Function.comp_apply] }⟩

/-- A distribution is coupled with itself for equality on its support. -/
theorem coupled_same_supp {α : Type} (p : PMF α) :
    Coupled p p fun a b => a = b ∧ a ∈ p.support := by
  refine ⟨p.map fun a => (a, a), ?_, ?_, ?_⟩
  · rw [PMF.map_comp]; exact PMF.map_id p
  · rw [PMF.map_comp]; exact PMF.map_id p
  · intro z hz
    rw [PMF.mem_support_map_iff] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    exact ⟨rfl, ha⟩

omit [Fintype S] [DecidableEq Sec] [Inhabited Sec] in
/-- An entry of the table after the symbolic key derivation at `j` is an entry before it or an
entry at `j`. -/
theorem sro_mem (O : W → W → W → Bool) (X : W) (tb : List (TInp Tr (W ⊕ W) × Sec))
    (j : TInp Tr (W ⊕ W)) : ∀ p ∈ (sro G O X tb j).support, ∀ q ∈ p.2, q ∈ tb ∨ q.1 = j := by
  intro p hp q hq
  unfold sro at hp
  split at hp
  · rw [PMF.support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact Or.inl hq
  · rw [PMF.support_map] at hp
    obtain ⟨v, -, rfl⟩ := hp
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Or.inr rfl
    · exact Or.inl hq

/-- The step of `kdf` from related states. -/
theorem red_kdf (j : ℕ) (x y : S) (s₁ : HSt S W Tr VK SK Sig Sec) (s₂ : RW S W Tr VK SK Sec)
    (z : TInp Tr W) (h : RCpl G Sg trs x y j s₁ s₂) :
    Coupled (hOx (tlsDHAlg G Sg trs) j x s₁ (.inr (.kdf z)))
      (redO G Sg trs j (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) s₂ (.inr (.kdf z)))
        fun z₁ z₂ => z₁.2.1.2 = true ∨ (z₁.1 = z₂.1 ∧ RCpl G Sg trs x y j z₁.2 z₂.2) := by
  obtain ⟨⟨⟨⟨c, inp, ph⟩, f⟩, fl⟩, cnt, idx⟩ := s₁
  have hph : ph = none := h.ph
  have hfl : fl = false := h.fl
  have hro : c.ro = s₂.c.ro.map (tinterpE G x) := h.ro
  subst hph hfl
  change Coupled (hO _ _ _) _ _
  rw [hO_adv G Sg trs _ _ rfl (fun _ _ h => by cases h) (fun _ _ => rfl)]
  have hr : CatCrypt.Crypto.PAKE.CPaceSquare.roAt c.ro z =
      (sro G (ddhOracle (gapDHDef G)) (G.pub x) s₂.c.ro ⟨z.lbl, z.tr, .inl z.dhe⟩).map
        fun p => (p.1, p.2.map (tinterpE G x)) := by
    rw [hro]
    exact roAt_tinterp G x s₂.c.ro ⟨z.lbl, z.tr, .inl z.dhe⟩
  simp only [realAdvK, lazyKDF, hr, PMF.map_comp, redO]
  refine coupled_map _ _ ((coupled_same_supp _).mono ?_)
  rintro p _ ⟨rfl, hp⟩
  refine Or.inr ⟨rfl, { h with ro := rfl, sym := ?_ }⟩
  intro q hq E hE hl
  rcases sro_mem G _ _ _ _ p hp q hq with hq | hq
  · exact h.sym q hq E hE hl
  · rw [hq] at hE
    simp at hE

/-- The step of `poll` from related states. -/
theorem red_poll (j : ℕ) (x y : S) (s₁ : HSt S W Tr VK SK Sig Sec) (s₂ : RW S W Tr VK SK Sec)
    (h : RCpl G Sg trs x y j s₁ s₂) :
    Coupled (hOx (tlsDHAlg G Sg trs) j x s₁ (.inr .poll))
      (redO G Sg trs j (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) s₂ (.inr .poll))
        fun z₁ z₂ => z₁.2.1.2 = true ∨ (z₁.1 = z₂.1 ∧ RCpl G Sg trs x y j z₁.2 z₂.2) := by
  obtain ⟨⟨⟨⟨c, inp, ph⟩, f⟩, fl⟩, cnt, idx⟩ := s₁
  have hph : ph = none := h.ph
  have hfl : fl = false := h.fl
  have hst : c.st = s₂.c.st := h.st
  subst hph hfl
  change Coupled (hO _ _ _) _ _
  rw [hO_adv G Sg trs _ _ rfl (fun _ _ h => by cases h) (fun _ _ => rfl)]
  simp only [realAdvK, redO, PMF.pure_map, hst, pollStep_eq]
  exact coupled_pure (Or.inr ⟨rfl, { h with st := rfl }⟩)

/-- The world with the indices at an event other than `hello`: the step of the simulated world,
with the flag and the indices unchanged. -/
theorem hO_nh (s₁ : HSt S W Tr VK SK Sig Sec) (e : TOEv W Tr Sig Sec)
    (hne : ∀ sid c, e ≠ .inr (.hello sid c))
    (hd : ∀ t t' : TSimSt S W Tr VK SK Sig Sec × St (TKey Sec), drawAt t t' e = none) :
    hO (tlsDHAlg G Sg trs) s₁ e =
      (simO (tlsDHAlg G Sg trs) s₁.1.1 e).map fun p => (p.1, ((p.2, s₁.1.2), s₁.2)) := by
  have hc : ∀ q, ¬ CollAt (tlsDHAlg G Sg trs) s₁.1.1 e q := by
    rintro q ⟨sid, c, _, _, _, _, _, _, _, _, _, hh, -⟩
    exact hne sid c hh
  simp only [hO, collO, OracleAdv.flagWhen, PMF.map_comp]
  congr 1
  funext p
  simp [hc, idxStep, hd]

omit [Fintype S] [SampleableType W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- A new session keeps the relation. -/
theorem rCpl_addSession {j : ℕ} {x y : S} {c : TRSt S W Tr VK SK Sec}
    {inp : Inst → Option (TInp Tr W)} {f : St (TKey Sec)} {cnt : ℕ} {idx : Inst → Option ℕ}
    {s₂ : RW S W Tr VK SK Sec} (h : RCpl G Sg trs x y j ((((c, inp, none), f), false), cnt, idx) s₂)
    (z : Inst) (peer : PartyId) (role : Role) :
    RCpl G Sg trs x y j
      (((({ c with st := addSession c.st z peer role }, inp, none), addSession f z peer role),
        false), cnt, idx)
      { s₂ with c := { s₂.c with st := addSession s₂.c.st z peer role }
                f := addSession s₂.f z peer role } := by
  have hst : c.st = s₂.c.st := h.st
  have hf : f = s₂.f := h.f
  subst hf
  have hsh := h.rsh z
  cases hx : s₂.c.st.recs z with
  | some r =>
    obtain ⟨rf, hfz⟩ : ∃ rf, s₂.f.recs z = some rf := by
      rw [hx] at hsh; cases h' : s₂.f.recs z <;> simp_all
    have e0 : addSession c.st z peer role = c.st := by simp [addSession, hst, hx]
    have e1 : addSession s₂.c.st z peer role = s₂.c.st := by simp [addSession, hx]
    have e2 : addSession s₂.f z peer role = s₂.f := by simp [addSession, hfz]
    rw [e0, e1, e2]
    exact h
  | none =>
    rw [hst]
    have hfz : s₂.f.recs z = none := by
      rw [hx] at hsh; cases h' : s₂.f.recs z <;> simp_all
    have hiz : s₂.inp z = none := by
      cases hi : s₂.inp z with
      | none => rfl
      | some ip =>
        obtain ⟨r, hr, -⟩ := h.inpKey z ip hi
        rw [hx] at hr; cases hr
    have hsz : s₂.c.srv z = none := by
      cases hs : s₂.c.srv z with
      | none => rfl
      | some p =>
        obtain ⟨r, hr, -⟩ := h.srvTr z p hs
        rw [hx] at hr; cases hr
    have hk : ∀ w, keyOf (addSession s₂.f z peer role) w = keyOf s₂.f w := by
      intro w
      unfold keyOf
      simp only [addSession, hfz, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      by_cases hw : w = z
      · subst hw; simp [hfz]
      · rw [Function.update_of_ne hw]
    simp only [addSession, hx, hfz, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hk ⊢
    have hne : ∀ {w : Inst} {r : Rec (TKey Sec)}, w ≠ z → s₂.c.st.recs w = some r →
        Function.update s₂.c.st.recs z (some ⟨peer, role, .fresh, none⟩) w = some r :=
      fun hw hr => by rw [Function.update_of_ne hw]; exact hr
    have hnz : ∀ {w : Inst} {ip : TInp Tr (W ⊕ W)}, s₂.inp w = some ip → w ≠ z := by
      rintro w ip hw rfl; rw [hiz] at hw; cases hw
    exact
    { fl := rfl
      ph := rfl
      st := rfl
      lt := h.lt
      eph := h.eph
      srv := h.srv
      log := h.log
      ro := h.ro
      inp := h.inp
      f := rfl
      cnt := h.cnt
      idx₁ := h.idx₁
      idx₂ := h.idx₂
      fcor := h.fcor
      rsh := fun w => by
        by_cases hw : w = z
        · subst hw; simp
        · simp only [Function.update_of_ne hw]; exact h.rsh w
      rst := fun w rc rf => by
        by_cases hw : w = z
        · subst hw; simp only [Function.update_self, Option.some.injEq]; rintro rfl rfl _; rfl
        · simp only [Function.update_of_ne hw]; exact h.rst w rc rf
      noticed := fun w hw => by
        by_cases hwz : w = z
        · subst hwz; exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl⟩
        · simp only [Function.update_of_ne hwz] at hw
          obtain ⟨n, hn, h1, h2⟩ := h.noticed w hw
          exact ⟨n, List.mem_append_left _ hn, h1, h2⟩
      inpKey := fun w ip hw => by
        obtain ⟨r, hr, hk'⟩ := h.inpKey w ip hw
        exact ⟨r, hne (hnz hw) hr, hk'⟩
      logY := h.logY
      srvY := fun sv r tSF Z cf hr hs hc => by
        have hsv : sv ≠ z := by rintro rfl; rw [hsz] at hs; cases hs
        simp only [Function.update_of_ne hsv] at hr
        exact h.srvY sv r tSF Z cf hr hs hc
      imp := fun w r hr hc => by
        by_cases hw : w = z
        · subst hw; simp only [Function.update_self, Option.some.injEq] at hr; subst hr
          cases hc
        · simp only [Function.update_of_ne hw] at hr
          exact h.imp w r hr hc
      comp := fun w r hr hc => by
        by_cases hw : w = z
        · subst hw; simp only [Function.update_self, Option.some.injEq] at hr; subst hr
          cases hc
        · simp only [Function.update_of_ne hw] at hr
          rcases h.comp w r hr hc with h1 | h1 | ⟨rc, h2, h3⟩
          · exact Or.inl h1
          · exact Or.inr (Or.inl h1)
          · exact Or.inr (Or.inr ⟨rc, hne hw h2, h3⟩)
      corr := fun w r hr hc hkey => by
        by_cases hw : w = z
        · subst hw; simp only [Function.update_self, Option.some.injEq] at hr; subst hr
          cases hc
        · simp only [Function.update_of_ne hw] at hr
          simp only [hk] at hkey
          exact h.corr w r hr hc hkey
      own := fun w ip hw => by
        obtain ⟨hl, r, hr, rest⟩ := h.own w ip hw
        exact ⟨hl, r, hne (hnz hw) hr, rest⟩
      keyed := fun w r hr hc => by
        by_cases hw : w = z
        · subst hw; simp only [Function.update_self, Option.some.injEq] at hr; subst hr
          cases hc
        · simp only [Function.update_of_ne hw] at hr
          exact h.keyed w r hr hc
      sym := fun p hp E hE hl => by
        obtain ⟨w, r, ip, hr, hc, hi, he⟩ := h.sym p hp E hE hl
        exact ⟨w, r, ip, by simp only [Function.update_of_ne (hnz hi)]; exact hr, hc, hi, he⟩
      pair := fun w r w' r' ip ip' hr hc hr' hc' hi hi' => by
        simp only [Function.update_of_ne (hnz hi)] at hr
        simp only [Function.update_of_ne (hnz hi')] at hr'
        exact h.pair w r w' r' ip ip' hr hc hr' hc' hi hi'
      srvTr := fun w p hs => by
        have hw : w ≠ z := by rintro rfl; rw [hsz] at hs; cases hs
        obtain ⟨r, hr, rest⟩ := h.srvTr w p hs
        exact ⟨r, hne hw hr, rest⟩
      ncomp := fun w r hr => by
        by_cases hw : w = z
        · subst hw; simp only [Function.update_self, Option.some.injEq] at hr; subst hr
          simp
        · simp only [Function.update_of_ne hw] at hr
          exact h.ncomp w r hr }

/-- The step of `newSession` from related states. -/
theorem red_newSession (j : ℕ) (x y : S) (s₁ : HSt S W Tr VK SK Sig Sec)
    (s₂ : RW S W Tr VK SK Sec) (sid : SessionId) (pid peer : PartyId) (role : Role)
    (h : RCpl G Sg trs x y j s₁ s₂) :
    Coupled (hOx (tlsDHAlg G Sg trs) j x s₁ (.inl (.newSession sid pid peer role)))
      (redO G Sg trs j (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) s₂
        (.inl (.newSession sid pid peer role))) fun z₁ z₂ =>
        z₁.2.1.2 = true ∨ (z₁.1 = z₂.1 ∧ RCpl G Sg trs x y j z₁.2 z₂.2) := by
  obtain ⟨⟨⟨⟨c, inp, ph⟩, f⟩, fl⟩, cnt, idx⟩ := s₁
  have hph : ph = none := h.ph
  have hfl : fl = false := h.fl
  subst hph hfl
  change Coupled (hO _ _ _) _ _
  rw [hO_nh G Sg trs _ _ (fun _ _ h => by cases h) (fun _ _ => rfl), simO_hon]
  have e1 : realHonK lazyKDF c (.newSession sid pid peer role) =
      PMF.pure (.ok, { c with st := addSession c.st (sid, pid) peer role }) := by
    simp only [realHonK, lazyKDF, PMF.pure_map]
    split_ifs with hn
    · rfl
    · have : addSession c.st (sid, pid) peer role = c.st := by
        cases hc : c.st.recs (sid, pid) <;> simp_all [addSession]
      rw [this]
  rw [e1, PMF.pure_map, PMF.pure_map]
  exact coupled_pure (Or.inr ⟨rfl, rCpl_addSession G Sg trs h (sid, pid) peer role⟩)

omit [Fintype S] [SampleableType W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- Related states agree on whether a session has a key. -/
theorem rCpl_keyOf {j : ℕ} {x y : S} {s₁ : HSt S W Tr VK SK Sig Sec}
    {s₂ : RW S W Tr VK SK Sec} (h : RCpl G Sg trs x y j s₁ s₂) (w : Inst) :
    (keyOf s₂.f w).isNone = (keyOf s₂.c.st w).isNone := by
  have hw := h.rsh w
  unfold keyOf
  rcases h1 : s₂.f.recs w with _ | ⟨_, _, _, _ | _⟩ <;>
    rcases h2 : s₂.c.st.recs w with _ | ⟨_, _, _, _ | _⟩ <;> simp_all [shp]

omit [Fintype S] [SampleableType W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- `corrupt pid` without `Pending` keeps the relation. -/
theorem rCpl_corrupt {j : ℕ} {x y : S} {c : TRSt S W Tr VK SK Sec}
    {inp : Inst → Option (TInp Tr W)} {cnt : ℕ} {idx : Inst → Option ℕ}
    {s₂ : RW S W Tr VK SK Sec}
    (h : RCpl G Sg trs x y j ((((c, inp, none), s₂.f), false), cnt, idx) s₂) (pid : PartyId)
    (hp : Pending s₂.c pid = false) (l : VK × SK) :
    RCpl G Sg trs x y j
      (((({ c with lt := Function.update c.lt pid (some l), st := corruptStep c.st pid }, inp,
        none), corruptStep s₂.f pid), false), cnt, idx)
      { s₂ with c := { s₂.c with lt := Function.update s₂.c.lt pid (some l),
                                 st := corruptStep s₂.c.st pid }
                f := corruptStep s₂.f pid } := by
  have hst : c.st = s₂.c.st := h.st
  have hlt : c.lt = s₂.c.lt := h.lt
  exact
  { h with
    st := by simp only [hst]
    lt := by simp only [hlt]
    f := rfl
    fcor := by simp only [corruptStep, h.fcor]
    comp := fun z r hr hc => by
      have hup : ∀ q, s₂.f.corrupt q = true → (corruptStep s₂.f pid).corrupt q = true := by
        intro q hq
        simp only [corruptStep, Function.update_apply]
        split_ifs <;> simp [hq]
      rcases h.comp z r hr hc with h1 | h1 | h1
      · exact Or.inl (hup _ h1)
      · exact Or.inr (Or.inl (hup _ h1))
      · exact Or.inr (Or.inr h1)
    corr := fun z r hr hc hkey => by
      have hr : s₂.f.recs z = some r := hr
      have hkey : keyOf s₂.f (z.1, r.peer) = none := hkey
      obtain ⟨h1, h2⟩ := h.corr z r hr hc hkey
      obtain ⟨ip, hip, -⟩ := h.keyed z r hr hc
      obtain ⟨rc, hrc, hk⟩ := h.inpKey z ip hip
      obtain ⟨n, hn, hn1, hn2⟩ := h.noticed z (by rw [hrc]; rfl)
      have hsh := h.rsh z
      rw [hr, hrc] at hsh
      simp only [Option.map_some, Option.some.injEq, shp, Prod.mk.injEq] at hsh
      have hkn : (keyOf s₂.c.st (z.1, rc.peer)).isNone = true := by
        rw [← hsh.1, ← rCpl_keyOf G Sg trs h, hkey]; rfl
      have hz : z.2 ≠ pid ∧ r.peer ≠ pid := by
        by_contra hcon
        have hpend : Pending s₂.c pid = true := by
          unfold Pending
          rw [List.any_eq_true]
          refine ⟨n, hn, ?_⟩
          have hz' : (n.sid, n.pid) = z := by rw [hn1, hn2]
          rw [hz', hrc]
          simp only [hk, Bool.true_and, hn2, ← hsh.1, hn1]
          grind
        rw [hp] at hpend
        cases hpend
      simp only [corruptStep, Function.update_apply, ite_eq_right hz.1, ite_eq_right hz.2]
      exact ⟨h1, h2⟩ }

/-- The step of `corrupt` from related states. -/
theorem red_corrupt (j : ℕ) (x y : S) (s₁ : HSt S W Tr VK SK Sig Sec) (s₂ : RW S W Tr VK SK Sec)
    (pid : PartyId) (h : RCpl G Sg trs x y j s₁ s₂) :
    Coupled (hOx (tlsDHAlg G Sg trs) j x s₁ (.inr (.corrupt pid)))
      (redO G Sg trs j (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) s₂ (.inr (.corrupt pid)))
        fun z₁ z₂ => z₁.2.1.2 = true ∨ (z₁.1 = z₂.1 ∧ RCpl G Sg trs x y j z₁.2 z₂.2) := by
  obtain ⟨⟨⟨⟨c, inp, ph⟩, f⟩, fl⟩, cnt, idx⟩ := s₁
  have hph : ph = none := h.ph
  have hfl : fl = false := h.fl
  have hst : c.st = s₂.c.st := h.st
  have hlt : c.lt = s₂.c.lt := h.lt
  have hf : f = s₂.f := h.f
  subst hph hfl hf
  change Coupled (hO _ _ _) _ _
  rw [hO_nh G Sg trs _ _ (fun _ _ h => by cases h) (fun _ _ => rfl), simO_corrupt]
  have hP : Pending c pid = Pending s₂.c pid := by unfold Pending; rw [hst]
  simp only [redO, hP]
  split_ifs with hp
  · rw [PMF.pure_map]
    exact coupled_pure (Or.inr ⟨rfl, h⟩)
  · have hR := rCpl_corrupt G Sg trs h pid (by simpa using hp)
    simp only [ltAt_eq, rlt, PMF.map_comp, hlt]
    cases hl : s₂.c.lt pid with
    | some l =>
      have hu : Function.update s₂.c.lt pid (some l) = s₂.c.lt := by
        rw [← hl, Function.update_eq_self]
      simp only [PMF.pure_map]
      refine coupled_pure (Or.inr ⟨rfl, ?_⟩)
      have := hR l
      simp only [hu] at this
      grind
    | none =>
      dsimp only
      simp only [PMF.map_comp]
      refine coupled_map _ _ ((coupled_same _).mono ?_)
      rintro l _ rfl
      grind

/-- `hello` that changes nothing in the copy: the answer, and the state with the stored output
cleared. -/
theorem hO_hello_same (a : HSt S W Tr VK SK Sig Sec) (sid : SessionId) (pid : PartyId)
    (o : TOut W VK SK Sig Sec)
    (ho : helloStep (tlsDHAlg G Sg trs) a.1.1.1.1 (sid, pid) = PMF.pure (o, a.1.1.1.1)) :
    hO (tlsDHAlg G Sg trs) a (.inr (.hello sid pid)) =
      PMF.pure (.inr o, ((((a.1.1.1.1, a.1.1.1.2.1, none), a.1.1.2), a.1.2), a.2)) := by
  have hC : ¬ CollAt (tlsDHAlg G Sg trs) a.1.1 (.inr (.hello sid pid))
      (.inr o, ((a.1.1.1.1, a.1.1.1.2.1, none), a.1.1.2)) := by
    rintro ⟨_, _, _, _, _, _, _, _, _, _, _, hh, h1, h2, -⟩
    simp only [Sum.inr.injEq, TEv.hello.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    cases h1.symm.trans h2
  simp only [hO, collO, OracleAdv.flagWhen, simO_hello, ho, PMF.pure_map, hC, decide_false,
    Bool.or_false]
  cases he : a.1.1.1.1.eph (sid, pid) <;> simp [idxStep, drawAt, he]

/-- `hello` at an initiator session without share in the world with the indices: the image of a
uniform secret. -/
theorem hO_hello_draw (a : HSt S W Tr VK SK Sig Sec) {sid : SessionId} {pid : PartyId}
    {r : Rec (TKey Sec)} (hr : a.1.1.1.1.st.recs (sid, pid) = some r) (hi : r.role = .initiator)
    (he : a.1.1.1.1.eph (sid, pid) = none) :
    hO (tlsDHAlg G Sg trs) a (.inr (.hello sid pid)) =
      (PMF.uniformFintype S).map (helloRes (tlsDHAlg G Sg trs) a sid pid) := by
  simp only [hO, collO, OracleAdv.flagWhen, simO_hello, PMF.map_comp]
  unfold helloStep
  simp only [hr, hi, ↓reduceIte, he, PMF.map_comp]
  rfl

omit [Fintype S] [SampleableType W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- A share drawn at the client session `z` that a server session naming `z`'s party as peer
already received is a collision. -/
theorem collAt_of {j : ℕ} {x y : S} {c : TRSt S W Tr VK SK Sec}
    {inp : Inst → Option (TInp Tr W)} {cnt : ℕ} {idx : Inst → Option ℕ}
    {s₂ : RW S W Tr VK SK Sec}
    (h : RCpl G Sg trs x y j ((((c, inp, none), s₂.f), false), cnt, idx) s₂) {z : Inst}
    (he : s₂.c.eph z = none) (xs : S)
    (q : TOOut W VK SK Sig Sec × (TSimSt S W Tr VK SK Sig Sec × St (TKey Sec)))
    (hq : q.2.1.1.eph z = some xs) {w : Inst} {r' : Rec (TKey Sec)} {tSF : Tr} {Z : W ⊕ W}
    {cf : Sec} {X' Ys : W} {vk : VK} {σ : Sig} {sf : Sec} (hr' : s₂.c.st.recs w = some r')
    (hz : (w.1, r'.peer) = z) (hs : s₂.c.srv w = some (tSF, Z, cf))
    (htr : tSF = trs.trSF (trs.trCV (trs.trCert (trs.tr1 w.1 r'.peer w.2 X' Ys) vk) σ) sf)
    (hX : X' = G.pub xs) :
    CollAt (tlsDHAlg G Sg trs) ((c, inp, none), s₂.f) (.inr (.hello z.1 z.2)) q := by
  subst hz
  obtain ⟨w1, w2⟩ := w
  have hsh := h.rsh (w1, w2)
  rw [hr'] at hsh
  obtain ⟨rf, hrf, hp⟩ : ∃ rf, s₂.f.recs (w1, w2) = some rf ∧ rf.peer = r'.peer := by
    cases h' : s₂.f.recs (w1, w2) <;> simp_all [shp]
  have hce : c.eph (w1, r'.peer) = none := by
    have := h.eph (w1, r'.peer)
    rw [he] at this
    exact this
  have hcs : c.srv (w1, w2) = some (tSF, X3DHSquareGDH.ev G x Z, cf) := by
    have := h.srv (w1, w2)
    rw [hs] at this
    exact this
  refine ⟨w1, r'.peer, xs, w2, rf, Ys, vk, σ, sf, X3DHSquareGDH.ev G x Z, cf, rfl, hce, hq, hrf,
    hp, ?_⟩
  rw [hcs, htr, hX]

omit [Fintype S] [SampleableType W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- The draw of the share of an initiator session keeps the relation, when no server session
naming it received the drawn share. -/
theorem rCpl_hello {j : ℕ} {x y : S} {c : TRSt S W Tr VK SK Sec}
    {inp : Inst → Option (TInp Tr W)} {cnt : ℕ} {idx : Inst → Option ℕ}
    {s₂ : RW S W Tr VK SK Sec}
    (h : RCpl G Sg trs x y j ((((c, inp, none), s₂.f), false), cnt, idx) s₂) {z : Inst}
    {r : Rec (TKey Sec)} (hx : s₂.c.st.recs z = some r) (hi : r.role = .initiator)
    (he : s₂.c.eph z = none) (o : Option S) (hj : cnt = j → o = none)
    (hcoll : ∀ w r' tSF Z cf X' Ys vk σ sf, s₂.c.st.recs w = some r' → (w.1, r'.peer) = z →
      s₂.c.srv w = some (tSF, Z, cf) →
      tSF = trs.trSF (trs.trCV (trs.trCert (trs.tr1 w.1 r'.peer w.2 X' Ys) vk) σ) sf →
      X' ≠ G.pub (o.getD x)) :
    RCpl G Sg trs x y j
      (((({ c with eph := Function.update c.eph z (some (o.getD x)) }, inp, none), s₂.f), false),
        cnt + 1, Function.update idx z (some cnt))
      { s₂ with c := { s₂.c with eph := Function.update s₂.c.eph z (some o) }
                hellos := s₂.hellos + 1 } := by
  have hshR : ∀ w, w ≠ z → shareR G (G.pub x)
      { s₂ with c := { s₂.c with eph := Function.update s₂.c.eph z (some o) }
                hellos := s₂.hellos + 1 } w = shareR G (G.pub x) s₂ w := fun w hw => by
    simp [shareR, Function.update_of_ne hw]
  have hiz : s₂.inp z = none := by
    cases hip : s₂.inp z with
    | none => rfl
    | some ip =>
      obtain ⟨-, r', hr', X', Ys, vk, σ, sf, -, hinit, -⟩ := h.own z ip hip
      rw [hx, Option.some.injEq] at hr'
      subst hr'
      have := hinit hi
      simp [shareR, he] at this
  have hez : ∀ w o', s₂.c.eph w = some o' → w ≠ z := by
    rintro w o' hw rfl; rw [he] at hw; cases hw
  exact
  { h with
    eph := fun w => by
      by_cases hw : w = z
      · subst hw; simp
      · simp only [Function.update_of_ne hw]; exact h.eph w
    cnt := congrArg (· + 1) h.cnt
    idx₁ := fun w hw => by
      by_cases hwz : w = z
      · subst hwz
        simp only [Function.update_self, Option.some.injEq] at hw ⊢
        rw [hj hw]
      · simp only [Function.update_of_ne hwz] at hw ⊢; exact h.idx₁ w hw
    idx₂ := fun w hw => by
      by_cases hwz : w = z
      · subst hwz; simp
      · simp only [Function.update_of_ne hwz] at hw ⊢; exact h.idx₂ w hw
    srvY := fun sv r' tSF Z cf hr' hs hc => by
      obtain ⟨o', ho', hv⟩ := h.srvY sv r' tSF Z cf hr' hs hc
      exact ⟨o', by simp only [Function.update_of_ne (hez _ _ ho')]; exact ho', hv⟩
    imp := fun w r' hr' hc => by
      obtain ⟨hrole, tSF, Z, cf, hs, X', Ys, vk, σ, sf, htr, hne⟩ := h.imp w r' hr' hc
      refine ⟨hrole, tSF, Z, cf, hs, X', Ys, vk, σ, sf, htr, ?_⟩
      by_cases hwz : (w.1, r'.peer) = z
      · have hX := hcoll w r' tSF Z cf X' Ys vk σ sf hr' hwz hs htr
        rw [hwz]
        simp only [shareR, Function.update_self, Option.map_some, ne_eq, Option.some.injEq]
        cases o <;> exact fun h' => hX h'.symm
      · rw [hshR _ hwz]; exact hne
    own := fun w ip hw => by
      have hwz : w ≠ z := by rintro rfl; rw [hiz] at hw; cases hw
      obtain ⟨hl, r', hr', X', Ys, vk, σ, sf, htr, hinit, hresp⟩ := h.own w ip hw
      exact ⟨hl, r', hr', X', Ys, vk, σ, sf, htr, fun hi' => by rw [hshR w hwz]; exact hinit hi',
        hresp⟩
    keyed := fun w r' hr' hc => by
      obtain ⟨ip, hip, o', ho', hv⟩ := h.keyed w r' hr' hc
      exact ⟨ip, hip, o', by simp only [Function.update_of_ne (hez _ _ ho')]; exact ho', hv⟩ }

/-- The step of `hello` from related states: the draw of the `j`-th share is the challenge share,
and a share that a server already received is a collision. -/
theorem red_hello (j : ℕ) (x y : S) (s₁ : HSt S W Tr VK SK Sig Sec) (s₂ : RW S W Tr VK SK Sec)
    (sid : SessionId) (pid : PartyId) (h : RCpl G Sg trs x y j s₁ s₂) :
    Coupled (hOx (tlsDHAlg G Sg trs) j x s₁ (.inr (.hello sid pid)))
      (redO G Sg trs j (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) s₂ (.inr (.hello sid pid)))
        fun z₁ z₂ => z₁.2.1.2 = true ∨ (z₁.1 = z₂.1 ∧ RCpl G Sg trs x y j z₁.2 z₂.2) := by
  obtain ⟨⟨⟨⟨c, inp, ph⟩, f⟩, fl⟩, cnt, idx⟩ := s₁
  have hph : ph = none := h.ph
  have hfl : fl = false := h.fl
  have hst : c.st = s₂.c.st := h.st
  have hf : f = s₂.f := h.f
  have hcnt : cnt = s₂.hellos := h.cnt
  subst hph hfl hf
  have heph : ∀ w, c.eph w = (s₂.c.eph w).map fun o => o.getD x := h.eph
  -- the steps that change nothing
  have hsame : ∀ o, helloStep (tlsDHAlg G Sg trs) c (sid, pid) = PMF.pure (o, c) →
      ¬ HUse (Sig := Sig) j ((((c, inp, none), s₂.f), false), cnt, idx) sid pid →
      hOx (tlsDHAlg G Sg trs) j x ((((c, inp, none), s₂.f), false), cnt, idx)
        (.inr (.hello sid pid)) =
          PMF.pure (.inr o, ((((c, inp, none), s₂.f), false), cnt, idx)) := by
    intro o ho hu
    simp only [hOx, ite_eq_right hu]
    exact hO_hello_same G Sg trs _ sid pid o ho
  cases hx : s₂.c.st.recs (sid, pid) with
  | none =>
    have hc : c.st.recs (sid, pid) = none := by rw [hst, hx]
    rw [hsame (.share none) (by simp [helloStep, hc]) (by rintro ⟨-, r, hr, -⟩; simp [hc] at hr)]
    simp only [redO, hx]
    exact coupled_pure (Or.inr ⟨rfl, h⟩)
  | some r =>
    have hc : c.st.recs (sid, pid) = some r := by rw [hst, hx]
    by_cases hi : r.role = .initiator
    swap
    · rw [hsame (.share none) (by simp [helloStep, hc, hi])
        (by rintro ⟨-, r', hr, hi', -⟩; rw [hc, Option.some.injEq] at hr; subst hr; exact hi hi')]
      simp only [redO, hx, hi, ite_false]
      exact coupled_pure (Or.inr ⟨rfl, h⟩)
    cases he : s₂.c.eph (sid, pid) with
    | some o =>
      have hce : c.eph (sid, pid) = some (o.getD x) := by rw [heph, he]; rfl
      rw [hsame (.share (some (G.pub (o.getD x)))) (by simp [helloStep, hc, hi, hce])
        (by rintro ⟨-, -, -, -, hn⟩; rw [hce] at hn; cases hn)]
      simp only [redO, hx, hi, ite_true, he]
      refine coupled_pure (Or.inr ⟨?_, h⟩)
      cases o <;> simp [shareR, he]
    | none =>
      have hce : c.eph (sid, pid) = none := by rw [heph, he]; rfl
      have hcoll : ∀ (o : Option S) (q : TOOut W VK SK Sig Sec × (TSimSt S W Tr VK SK Sig Sec ×
          St (TKey Sec))), q.2.1.1.eph (sid, pid) = some (o.getD x) →
          ¬ CollAt (tlsDHAlg G Sg trs) ((c, inp, none), s₂.f) (.inr (.hello sid pid)) q →
          ∀ w r' tSF Z cf X' Ys vk σ sf, s₂.c.st.recs w = some r' → (w.1, r'.peer) = (sid, pid) →
            s₂.c.srv w = some (tSF, Z, cf) →
            tSF = trs.trSF (trs.trCV (trs.trCert (trs.tr1 w.1 r'.peer w.2 X' Ys) vk) σ) sf →
            X' ≠ G.pub (o.getD x) := by
        intro o q hq hC w r' tSF Z cf X' Ys vk σ sf hr' hz hs htr hX
        exact hC (collAt_of G Sg trs h he (o.getD x) q hq hr' hz hs htr hX)
      by_cases hj : s₂.hellos = j
      · have hu : HUse (Sig := Sig) j ((((c, inp, none), s₂.f), false), cnt, idx) sid pid :=
          ⟨by rw [hcnt, hj], r, hc, hi, hce⟩
        simp only [hOx, ite_eq_left hu]
        simp only [redO, hx, hi, ite_true, he, hj]
        refine coupled_pure ?_
        simp only [helloRes]
        by_cases hC : CollAt (tlsDHAlg G Sg trs) ((c, inp, none), s₂.f) (.inr (.hello sid pid))
          (.inr (.share (some ((tlsDHAlg G Sg trs).pub x))),
            ({ c with eph := Function.update c.eph (sid, pid) (some x) }, inp, none), s₂.f)
        · left
          simp [hC]
        · right
          refine ⟨by simp, ?_⟩
          have hd : idxStep (Sig := Sig) ((c, inp, none), s₂.f)
              (({ c with eph := Function.update c.eph (sid, pid) (some x) }, inp, none), s₂.f)
              (.inr (.hello sid pid)) (cnt, idx) =
                (cnt + 1, Function.update idx (sid, pid) (some cnt)) := by
            simp [idxStep, drawAt, hce]
          rw [hd]
          simp only [hC, decide_false, Bool.or_false]
          have hR := rCpl_hello G Sg trs h hx hi he none (fun _ => rfl)
            (hcoll none _ (by simp) hC)
          rw [hj] at hR
          exact hR
      · have hu : ¬ HUse (Sig := Sig) j ((((c, inp, none), s₂.f), false), cnt, idx) sid pid
            := by rintro ⟨h1, -⟩; exact hj (by rw [← hcnt]; exact h1)
        simp only [hOx, ite_eq_right hu]
        rw [hO_hello_draw G Sg trs ((((c, inp, none), s₂.f), false), cnt, idx) hc hi hce]
        simp only [redO, hx, hi, ite_true, he, hj, ite_false]
        refine coupled_map _ _ ((coupled_same _).mono ?_)
        rintro xs _ rfl
        simp only [helloRes]
        by_cases hC : CollAt (tlsDHAlg G Sg trs) ((c, inp, none), s₂.f) (.inr (.hello sid pid))
          (.inr (.share (some ((tlsDHAlg G Sg trs).pub xs))),
            ({ c with eph := Function.update c.eph (sid, pid) (some xs) }, inp, none), s₂.f)
        · left
          simp [hC]
        · right
          refine ⟨by simp, ?_⟩
          have hd : idxStep (Sig := Sig) ((c, inp, none), s₂.f)
              (({ c with eph := Function.update c.eph (sid, pid) (some xs) }, inp, none), s₂.f)
              (.inr (.hello sid pid)) (cnt, idx) =
                (cnt + 1, Function.update idx (sid, pid) (some cnt)) := by
            simp [idxStep, drawAt, hce]
          rw [hd]
          simp only [hC, decide_false, Bool.or_false]
          exact rCpl_hello G Sg trs h hx hi he (some xs)
            (fun h' => absurd (by rw [← hcnt]; exact h') hj) (hcoll (some xs) _ (by simp) hC)

omit [Field S] [Fintype S] [SampleableType W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- The signing key pair in the world of the reduction, as the image of a draw. -/
theorem rlt_eq (s : RW S W Tr VK SK Sec) (pid : PartyId) :
    rlt Sg s pid = (match s.c.lt pid with
      | some l => PMF.pure l
      | none => Sg.keyDist).map fun l =>
        (l, { s with c := { s.c with lt := Function.update s.c.lt pid (some l) } }) := by
  unfold rlt
  cases hl : s.c.lt pid with
  | none => rfl
  | some l =>
    simp only [PMF.pure_map]
    congr
    rw [← hl, Function.update_eq_self]

omit [DecidableEq Sec] [Inhabited Sec] in
/-- `roAt_tinterp` at an input given by its components. -/
theorem roAt_tinterp' (x : S) (tb : List (TInp Tr (W ⊕ W) × Sec)) (lb : TLabel) (t : Tr)
    (Z : W ⊕ W) :
    CatCrypt.Crypto.PAKE.CPaceSquare.roAt (tb.map (tinterpE G x))
        ⟨lb, t, X3DHSquareGDH.ev G x Z⟩ =
      (sro G (ddhOracle (gapDHDef G)) (G.pub x) tb ⟨lb, t, Z⟩).map
        fun p => (p.1, p.2.map (tinterpE G x)) :=
  roAt_tinterp G x tb ⟨lb, t, Z⟩

omit [DecidableEq Sec] [Inhabited Sec] in
/-- `roAt_tinterp` at an input with a known value. -/
theorem roAt_tinterp_inl (x : S) (tb : List (TInp Tr (W ⊕ W) × Sec)) (lb : TLabel) (t : Tr)
    (w : W) :
    CatCrypt.Crypto.PAKE.CPaceSquare.roAt (tb.map (tinterpE G x)) ⟨lb, t, w⟩ =
      (sro G (ddhOracle (gapDHDef G)) (G.pub x) tb ⟨lb, t, .inl w⟩).map
        fun p => (p.1, p.2.map (tinterpE G x)) :=
  roAt_tinterp G x tb ⟨lb, t, .inl w⟩

omit [Field S] [SampleableType W] in
/-- A uniform scalar and its translate by `y` are coupled. -/
theorem coupled_shift {S : Type} [Field S] [Fintype S] (y : S) :
    Coupled (PMF.uniformFintype S) (PMF.uniformFintype S) fun a b => a = y + b := by
  refine ⟨(PMF.uniformFintype S).map fun v => (y + v, v), ?_, ?_, ?_⟩
  · rw [PMF.map_comp]
    exact PMF.uniformFintype_map_equiv (Equiv.addLeft y)
  · rw [PMF.map_comp]; exact PMF.map_id _
  · intro z hz
    rw [PMF.mem_support_map_iff] at hz
    obtain ⟨v, -, rfl⟩ := hz
    rfl

omit [Fintype S] [SampleableType W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- The keys of the functionality after a change of status at a record. -/
theorem keyOf_setRec_status (t : St (TKey Sec)) {z : Inst} {r : Rec (TKey Sec)}
    (hz : t.recs z = some r) (st' : Status) (w : Inst) :
    keyOf (setRec t z { r with status := st' }) w = keyOf t w := by
  unfold keyOf setRec
  by_cases hw : w = z
  · subst hw; simp [hz]
  · simp [Function.update_of_ne hw]

omit [Fintype S] [SampleableType W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- **The answer of a server session keeps the relation.** The server session `z` without key
and without answer records its transcript, its value `Z` and its client Finished, signs its
transcript, and takes the status `st'`: compromised when the share `X'` is not the share of its
client, its status otherwise. -/
theorem rCpl_srvRecv {j : ℕ} {x y : S} {c : TRSt S W Tr VK SK Sec}
    {inp : Inst → Option (TInp Tr W)} {cnt : ℕ} {idx : Inst → Option ℕ}
    {s₂ : RW S W Tr VK SK Sec}
    (h : RCpl G Sg trs x y j ((((c, inp, none), s₂.f), false), cnt, idx) s₂) {z : Inst}
    {r rf : Rec (TKey Sec)} (hx : s₂.c.st.recs z = some r) (hf : s₂.f.recs z = some rf)
    (hrole : r.role = .responder) (hk : r.key = none) (hsz : s₂.c.srv z = none)
    {X' Ys : W} {Z : W ⊕ W} (st' : Status)
    (hst1 : st' ≠ .compromised → shareR G (G.pub x) s₂ (z.1, r.peer) = some X')
    (hst2 : st' = .compromised → shareR G (G.pub x) s₂ (z.1, r.peer) ≠ some X')
    (hst3 : st' ≠ .completed) (lt' : PartyId → Option (VK × SK)) (vk : VK) (σ : Sig)
    (sf cf : Sec) (ro' : List (TInp Tr (W ⊕ W) × Sec))
    (hro : ∀ p ∈ ro', p ∈ s₂.c.ro ∨ p.1.lbl = .sfin ∨ p.1.lbl = .cfin) (vs' : List S)
    (hvs : ∀ v ∈ s₂.vs, v ∈ vs')
    (hXZ : X' = G.pub x → ∃ v ∈ vs', Ys = G.mul (G.pub y) (G.pub v) ∧ Z = .inr Ys) :
    RCpl G Sg trs x y j
      (((({ c with
          st := setRec c.st z { r with status := st' }
          lt := lt'
          srv := Function.update c.srv z (some (trs.trSF (trs.trCV (trs.trCert
            (trs.tr1 z.1 r.peer z.2 X' Ys) vk) σ) sf, X3DHSquareGDH.ev G x Z, cf))
          log := Function.update c.log z.2
            (trs.trCert (trs.tr1 z.1 r.peer z.2 X' Ys) vk :: c.log z.2)
          ro := ro'.map (tinterpE G x) }, inp, none), setRec s₂.f z { rf with status := st' }),
        false), cnt, idx)
      { s₂ with
        c := { s₂.c with
          st := setRec s₂.c.st z { r with status := st' }
          lt := lt'
          srv := Function.update s₂.c.srv z (some (trs.trSF (trs.trCV (trs.trCert
            (trs.tr1 z.1 r.peer z.2 X' Ys) vk) σ) sf, Z, cf))
          log := Function.update s₂.c.log z.2
            (trs.trCert (trs.tr1 z.1 r.peer z.2 X' Ys) vk :: s₂.c.log z.2)
          ro := ro' }
        f := setRec s₂.f z { rf with status := st' }
        vs := vs' } := by
  have hst : c.st = s₂.c.st := h.st
  have hlog : c.log = s₂.c.log := h.log
  have hiz : s₂.inp z = none := by
    cases hip : s₂.inp z with
    | none => rfl
    | some ip =>
      obtain ⟨r', hr', hk'⟩ := h.inpKey z ip hip
      rw [hx, Option.some.injEq] at hr'
      subst hr'
      rw [hk] at hk'
      cases hk'
  have hnz : ∀ {w : Inst} {ip : TInp Tr (W ⊕ W)}, s₂.inp w = some ip → w ≠ z := by
    rintro w ip hw rfl; rw [hiz] at hw; cases hw
  have hrst : r.status = rf.status := by
    have hsh := h.rsh z
    rw [hx, hf] at hsh
    simp only [Option.map_some, Option.some.injEq, shp, Prod.mk.injEq] at hsh
    exact h.rst z r rf hx hf (by cases h' : rf.key <;> simp_all)
  have hsh0 : rf.peer = r.peer ∧ rf.role = r.role ∧ rf.key.isSome = r.key.isSome := by
    have hsh := h.rsh z
    rw [hx, hf] at hsh
    simpa only [Option.map_some, Option.some.injEq, shp, Prod.mk.injEq] using hsh
  have hfc : ∀ w r', s₂.f.recs w = some r' → r'.status = .compromised → w ≠ z := by
    intro w r' hw hc hwz
    rw [hwz, hf, Option.some.injEq] at hw
    subst hw
    obtain ⟨-, tSF, Z₀, cf₀, hs, -⟩ := h.imp z r hx (by rw [hrst, hc])
    rw [hsz] at hs; cases hs
  have hR : ∀ w, (setRec s₂.c.st z { r with status := st' }).recs w =
      if w = z then some { r with status := st' } else s₂.c.st.recs w := by
    intro w; simp only [setRec, Function.update_apply]
  have hRf : ∀ w, (setRec s₂.f z { rf with status := st' }).recs w =
      if w = z then some { rf with status := st' } else s₂.f.recs w := by
    intro w; simp only [setRec, Function.update_apply]
  have hshR : ∀ w, shareR G (G.pub x) { s₂ with
        c := { s₂.c with
          st := setRec s₂.c.st z { r with status := st' }
          lt := lt'
          srv := Function.update s₂.c.srv z (some (trs.trSF (trs.trCV (trs.trCert
            (trs.tr1 z.1 r.peer z.2 X' Ys) vk) σ) sf, Z, cf))
          log := Function.update s₂.c.log z.2
            (trs.trCert (trs.tr1 z.1 r.peer z.2 X' Ys) vk :: s₂.c.log z.2)
          ro := ro' }
        f := setRec s₂.f z { rf with status := st' }
        vs := vs' } w = shareR G (G.pub x) s₂ w := fun _ => rfl
  exact
  { fl := rfl
    ph := rfl
    st := by rw [hst]
    lt := rfl
    eph := h.eph
    srv := fun w => by
      by_cases hw : w = z
      · subst hw; simp
      · simp only [Function.update_of_ne hw]; exact h.srv w
    log := by rw [hlog]
    ro := rfl
    inp := h.inp
    f := rfl
    cnt := h.cnt
    idx₁ := h.idx₁
    idx₂ := h.idx₂
    fcor := h.fcor
    rsh := fun w => by
      rw [hR, hRf]
      split_ifs
      · simp [shp, hsh0.1, hsh0.2.1, hsh0.2.2]
      · exact h.rsh w
    rst := fun w rc rf' => by
      rw [hR, hRf]
      split_ifs
      · rintro ⟨⟩ ⟨⟩ _; rfl
      · exact h.rst w rc rf'
    noticed := fun w hw => by
      rw [hR] at hw
      split_ifs at hw with hwz
      · subst hwz; exact h.noticed w (by rw [hx]; rfl)
      · exact h.noticed w hw
    inpKey := fun w ip hw => by
      obtain ⟨r', hr', hk'⟩ := h.inpKey w ip hw
      refine ⟨r', ?_, hk'⟩
      rw [hR, ite_eq_right (hnz hw)]; exact hr'
    logY := fun p t ht => by
      by_cases hp : p = z.2
      · subst hp
        simp only [Function.update_self, List.mem_cons] at ht
        rcases ht with rfl | ht
        · refine ⟨z.1, r.peer, z.2, X', Ys, vk, rfl, fun hX => ?_⟩
          obtain ⟨v, hv, hYs, -⟩ := hXZ hX
          exact ⟨v, hv, hYs⟩
        · obtain ⟨a, b, d, X'', Ys', vk', h1, h2⟩ := h.logY _ t ht
          refine ⟨a, b, d, X'', Ys', vk', h1, fun hX => ?_⟩
          obtain ⟨v, hv, h3⟩ := h2 hX
          exact ⟨v, hvs v hv, h3⟩
      · simp only [Function.update_of_ne hp] at ht
        obtain ⟨a, b, d, X'', Ys', vk', h1, h2⟩ := h.logY p t ht
        refine ⟨a, b, d, X'', Ys', vk', h1, fun hX => ?_⟩
        obtain ⟨v, hv, h3⟩ := h2 hX
        exact ⟨v, hvs v hv, h3⟩
    srvY := fun sv r' tSF Z' cf' hr' hs hc => by
      by_cases hw : sv = z
      · subst hw
        simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨-, rfl, -⟩ := hs
        rw [hR, ite_eq_left rfl, Option.some.injEq] at hr'
        subst hr'
        have hsh := hst1 hc
        simp only [shareR, Option.map_eq_some_iff] at hsh
        obtain ⟨o, ho, hoX⟩ := hsh
        refine ⟨o, ho, fun hon => ?_⟩
        subst hon
        obtain ⟨v, hv, hYs, hZ⟩ := hXZ hoX.symm
        exact ⟨v, hv, by rw [hZ, hYs]⟩
      · simp only [Function.update_of_ne hw] at hs
        rw [hR, ite_eq_right hw] at hr'
        obtain ⟨o, ho, hv⟩ := h.srvY sv r' tSF Z' cf' hr' hs hc
        refine ⟨o, ho, fun hon => ?_⟩
        obtain ⟨v, hv', h3⟩ := hv hon
        exact ⟨v, hvs v hv', h3⟩
    imp := fun w r' hr' hc => by
      by_cases hw : w = z
      · subst hw
        rw [hR, ite_eq_left rfl, Option.some.injEq] at hr'
        subst hr'
        refine ⟨hrole, _, Z, cf, by simp, X', Ys, vk, σ, sf, rfl, ?_⟩
        rw [hshR]
        exact hst2 hc
      · rw [hR, ite_eq_right hw] at hr'
        obtain ⟨h1, tSF, Z', cf', hs, rest⟩ := h.imp w r' hr' hc
        exact ⟨h1, tSF, Z', cf', by simp only [Function.update_of_ne hw]; exact hs, rest⟩
    comp := fun w r' hr' hc => by
      by_cases hw : w = z
      · subst hw
        rw [hRf, ite_eq_left rfl, Option.some.injEq] at hr'
        subst hr'
        exact Or.inr (Or.inr ⟨{ r with status := st' }, by rw [hR, ite_eq_left rfl], hc⟩)
      · rw [hRf, ite_eq_right hw] at hr'
        rcases h.comp w r' hr' hc with h1 | h1 | ⟨rc, h2, h3⟩
        · exact Or.inl h1
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr ⟨rc, by rw [hR, ite_eq_right hw]; exact h2, h3⟩)
    corr := fun w r' hr' hc hkey => by
      by_cases hw : w = z
      · subst hw
        rw [hRf, ite_eq_left rfl, Option.some.injEq] at hr'
        subst hr'
        exact absurd hc hst3
      · rw [hRf, ite_eq_right hw] at hr'
        have hkey' : keyOf s₂.f (w.1, r'.peer) = none := by
          rw [← keyOf_setRec_status s₂.f hf st']; exact hkey
        exact h.corr w r' hr' hc hkey'
    own := fun w ip hw => by
      obtain ⟨hl, r', hr', X'', Ys', vk', σ', sf', htr, hinit, hresp⟩ := h.own w ip hw
      have hwz := hnz hw
      refine ⟨hl, r', by rw [hR, ite_eq_right hwz]; exact hr', X'', Ys', vk', σ', sf', htr, hinit,
        fun hr'' => ?_⟩
      obtain ⟨cf', hcf⟩ := hresp hr''
      exact ⟨cf', by simp only [Function.update_of_ne hwz]; exact hcf⟩
    keyed := fun w r' hr' hc => by
      by_cases hw : w = z
      · subst hw
        rw [hRf, ite_eq_left rfl, Option.some.injEq] at hr'
        subst hr'
        exact absurd hc hst3
      · rw [hRf, ite_eq_right hw] at hr'
        obtain ⟨ip, hip, o, ho, hv⟩ := h.keyed w r' hr' hc
        refine ⟨ip, hip, o, ho, fun hon => ?_⟩
        obtain ⟨v, hv', h3⟩ := hv hon
        exact ⟨v, hvs v hv', h3⟩
    sym := fun p hp E hE hl => by
      rcases hro p hp with hp | hp | hp
      · obtain ⟨w, r', ip, hr', hc, hi, he⟩ := h.sym p hp E hE hl
        exact ⟨w, r', ip, by rw [hRf, ite_eq_right (hfc w r' hr' hc)]; exact hr', hc, hi, he⟩
      · rcases hl with hl | hl | hl | hl <;> rw [hl] at hp <;> cases hp
      · rcases hl with hl | hl | hl | hl <;> rw [hl] at hp <;> cases hp
    pair := fun w r' w' r'' ip ip' hr' hc hr'' hc' hi hi' => by
      rw [hRf, ite_eq_right (hnz hi)] at hr'
      rw [hRf, ite_eq_right (hnz hi')] at hr''
      exact h.pair w r' w' r'' ip ip' hr' hc hr'' hc' hi hi'
    srvTr := fun w p hs => by
      by_cases hw : w = z
      · subst hw
        simp only [Function.update_self, Option.some.injEq] at hs
        subst hs
        exact ⟨{ r with status := st' }, by rw [hR, ite_eq_left rfl], hrole, X', Ys, vk, σ, sf, rfl⟩
      · simp only [Function.update_of_ne hw] at hs
        obtain ⟨r', hr', rest⟩ := h.srvTr w p hs
        exact ⟨r', by rw [hR, ite_eq_right hw]; exact hr', rest⟩
    ncomp := fun w r' hr' => by
      rw [hR] at hr'
      split_ifs at hr' with hw
      · cases hr'; exact hst3
      · exact h.ncomp w r' hr' }

/-- The step of `srvRecv` from related states: the server exponent is `y + v` for the
rerandomisation exponent `v` when the server receives the challenge share. -/
theorem red_srvRecv (j : ℕ) (x y : S) (s₁ : HSt S W Tr VK SK Sig Sec)
    (s₂ : RW S W Tr VK SK Sec) (sid : SessionId) (pid : PartyId) (X' : W)
    (h : RCpl G Sg trs x y j s₁ s₂) :
    Coupled (hOx (tlsDHAlg G Sg trs) j x s₁ (.inr (.srvRecv sid pid X')))
      (redO G Sg trs j (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) s₂
        (.inr (.srvRecv sid pid X'))) fun z₁ z₂ =>
        z₁.2.1.2 = true ∨ (z₁.1 = z₂.1 ∧ RCpl G Sg trs x y j z₁.2 z₂.2) := by
  obtain ⟨⟨⟨⟨c, inp, ph⟩, f⟩, fl⟩, cnt, idx⟩ := s₁
  have hph : ph = none := h.ph
  have hfl : fl = false := h.fl
  have hst : c.st = s₂.c.st := h.st
  have hlt : c.lt = s₂.c.lt := h.lt
  have hf : f = s₂.f := h.f
  subst hph hfl hf
  have hsrv : ∀ w, c.srv w =
      (s₂.c.srv w).map fun p => (p.1, X3DHSquareGDH.ev G x p.2.1, p.2.2) := h.srv
  have hro : c.ro = s₂.c.ro.map (tinterpE G x) := h.ro
  have hshare : ∀ w, shareOf (tlsDHAlg G Sg trs) c w = shareR G (G.pub x) s₂ w := by
    intro w
    have he : c.eph w = (s₂.c.eph w).map fun o => o.getD x := h.eph w
    simp only [shareOf, shareR, he, Option.map_map]
    rcases s₂.c.eph w with _ | _ | _ <;> rfl
  change Coupled (hO _ _ _) _ _
  rw [hO_nh G Sg trs _ _ (fun _ _ h => by cases h) (fun _ _ => rfl),
    simO_srvRecv _ _ (sid, pid) X', PMF.map_comp]
  simp only [redO]
  cases hx : s₂.c.st.recs (sid, pid) with
  | none =>
    have hc : c.st.recs (sid, pid) = none := by rw [hst, hx]
    have hI : Impersonated (tlsDHAlg G Sg trs) c (sid, pid) X' = false := by
      simp [Impersonated, hc]
    simp only [srvRecvK, srvRecvR, hc, hx, hI, PMF.pure_map, Bool.false_eq_true, ite_false]
    exact coupled_pure (Or.inr ⟨rfl, h⟩)
  | some r =>
    have hc : c.st.recs (sid, pid) = some r := by rw [hst, hx]
    have hsI : (c.srv (sid, pid)).isNone = (s₂.c.srv (sid, pid)).isNone := by
      rw [hsrv]; cases s₂.c.srv (sid, pid) <;> rfl
    by_cases hcond : r.role = .responder ∧ r.key.isNone = true ∧
      (s₂.c.srv (sid, pid)).isNone = true
    swap
    · have hcond' : ¬ (r.role = .responder ∧ r.key.isNone = true ∧
          (c.srv (sid, pid)).isNone = true) := by rwa [hsI]
      have hI : Impersonated (tlsDHAlg G Sg trs) c (sid, pid) X' = false := by
        simp only [Impersonated, hc, decide_eq_false_iff_not]
        exact fun h' => hcond' ⟨h'.1, h'.2.1, h'.2.2.1⟩
      simp only [srvRecvK, srvRecvR, hc, hx, hcond, hcond', hI, ite_false, PMF.pure_map,
        Bool.false_eq_true]
      exact coupled_pure (Or.inr ⟨rfl, h⟩)
    have hcond' : r.role = .responder ∧ r.key.isNone = true ∧
        (c.srv (sid, pid)).isNone = true := by rwa [hsI]
    have hI : Impersonated (tlsDHAlg G Sg trs) c (sid, pid) X' =
        decide (shareR G (G.pub x) s₂ (sid, r.peer) ≠ some X') := by
      simp only [Impersonated, hc, hcond'.1, hcond'.2.1, hcond'.2.2, true_and, hshare]
    simp only [srvRecvK, srvRecvR, hc, hx, ite_eq_left hcond, ite_eq_left hcond', hI, ltAt_eq,
      rlt_eq, hlt, PMF.map_bind, PMF.bind_map]
    refine coupled_bind (coupled_same _) ?_
    rintro l _ rfl
    -- the records of the server session
    have hk : r.key = none := Option.isNone_iff_eq_none.mp hcond.2.1
    have hsz : s₂.c.srv (sid, pid) = none := Option.isNone_iff_eq_none.mp hcond.2.2
    obtain ⟨rf, hf⟩ : ∃ rf, s₂.f.recs (sid, pid) = some rf := by
      have hsh := h.rsh (sid, pid)
      rw [hx] at hsh
      cases h' : s₂.f.recs (sid, pid) <;> simp_all
    have hrst : r.status = rf.status := by
      have hsh := h.rsh (sid, pid)
      rw [hx, hf] at hsh
      simp only [Option.map_some, Option.some.injEq, shp, Prod.mk.injEq] at hsh
      exact h.rst _ r rf hx hf (by cases h' : rf.key <;> simp_all)
    have hrole' : rf.role = r.role := by
      have hsh := h.rsh (sid, pid)
      rw [hx, hf] at hsh
      simp only [Option.map_some, Option.some.injEq, shp, Prod.mk.injEq] at hsh
      exact hsh.2.1
    have hkf : rf.key = none := by
      have hsh := h.rsh (sid, pid)
      rw [hx, hf] at hsh
      simp only [Option.map_some, Option.some.injEq, shp, Prod.mk.injEq, hk] at hsh
      cases h' : rf.key <;> simp_all
    have hfresh : r.status = .fresh := by
      have h1 := h.ncomp _ r hx
      have h2 : r.status ≠ .compromised := fun hc' => by
        obtain ⟨-, tSF, Z₀, cf₀, hs, -⟩ := h.imp _ r hx hc'
        rw [hsz] at hs; cases hs
      cases hs : r.status <;> simp_all
    have eS : ∀ t : St (TKey Sec), ∀ r' : Rec (TKey Sec), t.recs (sid, pid) = some r' →
        r'.role = .responder → r'.status = .fresh → r'.key = none →
        impStepOf srvImp t (sid, pid) = setRec t (sid, pid) { r' with status := .compromised } := by
      intro t r' ht h1 h2 h3
      simp [impStepOf, impStep, srvImp, ht, h1, h2, h3]
    have eN : ∀ t : St (TKey Sec), ∀ r' : Rec (TKey Sec), t.recs (sid, pid) = some r' →
        setRec t (sid, pid) { r' with status := r'.status } = t := by
      intro t r' ht
      simp only [setRec]
      rw [show ({ r' with status := r'.status } : Rec (TKey Sec)) = r' from rfl, ← ht,
        Function.update_eq_self]
    simp only [Function.comp_apply, PMF.map_bind, lazyKDF]
    have hcpl : Coupled (PMF.uniformFintype S) (PMF.uniformFintype S) fun a v =>
        G.pub a = (if X' = G.pub x then G.mul (G.pub y) (G.pub v) else G.pub v) ∧
        G.exp X' a = X3DHSquareGDH.ev G x (if X' = G.pub x then
          Sum.inr (if X' = G.pub x then G.mul (G.pub y) (G.pub v) else G.pub v)
          else Sum.inl (G.exp X' v)) := by
      by_cases hX : X' = G.pub x
      · refine (coupled_shift y).mono ?_
        rintro a v rfl
        subst hX
        simp only [ite_true, X3DHSquareGDH.ev]
        refine ⟨(G.mul_pub y v).symm, ?_⟩
        rw [G.mul_pub, G.exp_pub, G.exp_pub, mul_comm]
      · refine (coupled_same _).mono ?_
        rintro a v rfl
        simp [hX, X3DHSquareGDH.ev]
    refine coupled_bind hcpl ?_
    rintro a v ⟨hY, hZ⟩
    generalize hYs : (if X' = G.pub x then G.mul (G.pub y) (G.pub v) else G.pub v) = Ys at hY hZ ⊢
    generalize hZs : (if X' = G.pub x then Sum.inr Ys else Sum.inl (G.exp X' v)) = Z at hZ ⊢
    generalize hvs : (if X' = G.pub x then v :: s₂.vs else s₂.vs) = vs'
    have hXZ : X' = G.pub x → ∃ v' ∈ vs', Ys = G.mul (G.pub y) (G.pub v') ∧ Z = .inr Ys := by
      intro hX
      rw [ite_eq_left hX] at hYs hZs hvs
      exact ⟨v, by rw [← hvs]; exact List.mem_cons_self .., hYs.symm, hZs.symm⟩
    have hvs' : ∀ v' ∈ s₂.vs, v' ∈ vs' := by
      intro v' hv'
      rw [← hvs]
      split_ifs
      · exact List.mem_cons_of_mem _ hv'
      · exact hv'
    rw [hY, hZ]
    refine coupled_bind (coupled_same _) ?_
    rintro σ _ rfl
    rw [hro, roAt_tinterp' G x, PMF.bind_map]
    refine coupled_bind (coupled_same_supp _) ?_
    rintro sf _ ⟨rfl, hsf⟩
    simp only [Function.comp_apply]
    rw [roAt_tinterp' G x, PMF.map_comp, PMF.map_comp]
    refine coupled_map _ _ ((coupled_same_supp _).mono ?_)
    rintro cf _ ⟨rfl, hcf⟩
    refine Or.inr ⟨rfl, ?_⟩
    have hro' : ∀ p ∈ cf.2, p ∈ s₂.c.ro ∨ p.1.lbl = .sfin ∨ p.1.lbl = .cfin := by
      intro p hp
      rcases sro_mem G _ _ _ _ cf hcf p hp with hp | hp
      · rcases sro_mem G _ _ _ _ sf hsf p hp with hp | hp
        · exact Or.inl hp
        · exact Or.inr (Or.inl (by rw [hp]))
      · exact Or.inr (Or.inr (by rw [hp]))
    simp only [Function.comp_apply]
    by_cases hb : shareR G (G.pub x) s₂ (sid, r.peer) = some X'
    · have hd : decide (shareR G (G.pub x) s₂ (sid, r.peer) ≠ some X') = false := by simp [hb]
      simp only [hd, Bool.false_eq_true, ite_false]
      have hR := rCpl_srvRecv G Sg trs h hx hf hcond.1 hk hsz r.status (fun _ => hb)
        (fun h' => absurd h' (by rw [hfresh]; simp)) (by rw [hfresh]; simp)
        (Function.update s₂.c.lt pid (some l)) l.1 σ sf.1 cf.1 cf.2 hro' vs' hvs' hXZ
      have e1 : setRec s₂.c.st (sid, pid)
          { peer := r.peer, role := r.role, status := r.status, key := r.key } = s₂.c.st :=
        eN _ _ hx
      have e2 : setRec c.st (sid, pid)
          { peer := r.peer, role := r.role, status := r.status, key := r.key } = c.st :=
        eN _ _ hc
      have e3 : setRec s₂.f (sid, pid)
          { peer := rf.peer, role := rf.role, status := r.status, key := rf.key } = s₂.f := by
        rw [hrst]; exact eN _ _ hf
      rw [e1, e2, e3] at hR
      exact hR
    · have hd : decide (shareR G (G.pub x) s₂ (sid, r.peer) ≠ some X') = true := by simp [hb]
      simp only [hd, ite_true]
      rw [eS c.st r hc hcond.1 hfresh hk, eS s₂.c.st r hx hcond.1 hfresh hk,
        eS s₂.f rf hf (by rw [hrole']; exact hcond.1) (by rw [← hrst]; exact hfresh) hkf]
      exact rCpl_srvRecv G Sg trs h hx hf hcond.1 hk hsz .compromised (fun h' => absurd rfl h')
        (fun _ => hb) (by simp) (Function.update s₂.c.lt pid (some l)) l.1 σ sf.1 cf.1 cf.2 hro'
        vs' hvs' hXZ

omit [Fintype S] [SampleableType W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- With injective transcript operations, the transcript up to server Finished determines its
protocol session, its parties and its shares. -/
theorem trInj_shape (hT : TrInj trs) {a a' : SessionId} {b d b' d' : PartyId} {X₁ Y₁ X₂ Y₂ : W}
    {vk vk' : VK} {σ σ' : Sig} {sf sf' : Sec}
    (h : trs.trSF (trs.trCV (trs.trCert (trs.tr1 a b d X₁ Y₁) vk) σ) sf =
      trs.trSF (trs.trCV (trs.trCert (trs.tr1 a' b' d' X₂ Y₂) vk') σ') sf') :
    a = a' ∧ b = b' ∧ d = d' ∧ X₁ = X₂ ∧ Y₁ = Y₂ := by
  obtain ⟨h, -⟩ := hT.2.2.2.1 _ _ _ _ h
  obtain ⟨h, -⟩ := hT.2.2.1 _ _ _ _ h
  obtain ⟨h, -⟩ := hT.2.1 _ _ _ _ h
  exact hT.1 _ _ _ _ _ _ _ _ _ _ h

omit [Fintype S] [SampleableType W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- **A recorded input on the transcript of another session names its partner.** With injective
transcript operations, a session `w ≠ z` whose recorded input has the transcript `tSF` of `z` is
the session of the peer of `z`, names `z`'s party as its peer, has the other role, and has the
same client share. -/
theorem partner_of (hT : TrInj trs) {j : ℕ} {x y : S} {s₁ : HSt S W Tr VK SK Sig Sec}
    {s₂ : RW S W Tr VK SK Sec} (h : RCpl G Sg trs x y j s₁ s₂) {z : Inst} {r : Rec (TKey Sec)}
    {tSF : Tr} {X' Ys : W} {vk : VK} {σ : Sig} {sf : Sec}
    (htr : tSF = trs.trSF (trs.trCV (trs.trCert (trs.tr1 z.1
      (if r.role = .initiator then z.2 else r.peer) (if r.role = .initiator then r.peer else z.2)
      X' Ys) vk) σ) sf)
    {w : Inst} {ip : TInp Tr (W ⊕ W)} (hw : w ≠ z) (hi : s₂.inp w = some ip) (he : ip.tr = tSF) :
    ∃ rw, s₂.c.st.recs w = some rw ∧ w = (z.1, r.peer) ∧ rw.peer = z.2 ∧ rw.role ≠ r.role ∧
      (rw.role = .initiator → shareR G (G.pub x) s₂ w = some X') ∧
      (rw.role = .responder → ∃ cf, s₂.c.srv w = some (tSF, ip.dhe, cf)) := by
  obtain ⟨-, rw, hrw, X'', Ys', vk', σ', sf', htr', hin, hre⟩ := h.own w ip hi
  rw [he, htr] at htr'
  obtain ⟨h1, h2, h3, h4, -⟩ := trInj_shape trs hT htr'
  obtain ⟨z1, z2⟩ := z
  obtain ⟨w1, w2⟩ := w
  simp only at h1 h2 h3 hw ⊢
  subst h1 h4
  refine ⟨rw, hrw, ?_⟩
  cases hr : r.role <;> cases hrr : rw.role <;> simp only [hr, hrr, ite_true, reduceCtorEq,
    ite_false] at h2 h3 hin hre
  · exact absurd (by rw [h2]) hw
  · exact ⟨by rw [h3], h2.symm, by simp, by simp, fun _ => by rw [← he]; exact hre trivial⟩
  · exact ⟨by rw [h2], h3.symm, by simp, fun _ => hin trivial, by simp⟩
  · exact absurd (by rw [h3]) hw

omit [Fintype S] [SampleableType W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- **The completion of a session keeps the relation.** The session `z` without key, with the
recorded input `⟨cap, tSF, Z⟩` on a transcript of its own, receives a key in the copy and in the
functionality, completed unless exposed; the table of the reduction gains entries only at the
stage inputs of `z` when `z` is exposed. -/
theorem rCpl_deliver (hT : TrInj trs) {j : ℕ} {x y : S} {c : TRSt S W Tr VK SK Sec}
    {inp : Inst → Option (TInp Tr W)} {cnt : ℕ} {idx : Inst → Option ℕ}
    {s₂ : RW S W Tr VK SK Sec}
    (h : RCpl G Sg trs x y j ((((c, inp, none), s₂.f), false), cnt, idx) s₂) {z : Inst}
    {r rf : Rec (TKey Sec)} (hx : s₂.c.st.recs z = some r) (hf : s₂.f.recs z = some rf)
    (hk : r.key = none) {tSF : Tr} {Z : W ⊕ W} {X' Ys : W} {vk : VK} {σ : Sig} {sf : Sec}
    (htr : tSF = trs.trSF (trs.trCV (trs.trCert (trs.tr1 z.1
      (if r.role = .initiator then z.2 else r.peer) (if r.role = .initiator then r.peer else z.2)
      X' Ys) vk) σ) sf)
    (hinit : r.role = .initiator → shareR G (G.pub x) s₂ z = some X')
    (hresp : r.role = .responder → ∃ cf', s₂.c.srv z = some (tSF, Z, cf'))
    (hkey : ¬ Exposed s₂.c.st z r → ∃ o, s₂.c.eph (clientOf z r) = some o ∧
      (o = none → ∃ v ∈ s₂.vs, Z = .inr (G.mul (G.pub y) (G.pub v))))
    (k kk : TKey Sec) (st' : Status)
    (hst' : st' = if Exposed s₂.f z rf then .compromised else .completed)
    (ro₂ : List (TInp Tr (W ⊕ W) × Sec))
    (hro : ∀ p ∈ ro₂, p ∈ s₂.c.ro ∨ (Exposed s₂.c.st z r ∧
      ExtIn (tlsDHAlg G Sg trs) (tinterp G x ⟨.cap, tSF, Z⟩) (tinterp G x p.1))) :
    RCpl G Sg trs x y j
      (((({ c with st := setRec c.st z { r with key := some k }, ro := ro₂.map (tinterpE G x) },
          Function.update inp z (some ⟨.cap, tSF, X3DHSquareGDH.ev G x Z⟩), none),
        setRec s₂.f z { rf with key := some kk, status := st' }), false), cnt, idx)
      { s₂ with
        c := { s₂.c with st := setRec s₂.c.st z { r with key := some k }, ro := ro₂ }
        inp := Function.update s₂.inp z (some ⟨.cap, tSF, Z⟩)
        f := setRec s₂.f z { rf with key := some kk, status := st' } } := by
  have hst : c.st = s₂.c.st := h.st
  have hsh0 : rf.peer = r.peer ∧ rf.role = r.role ∧ rf.key.isSome = r.key.isSome := by
    have hsh := h.rsh z
    rw [hx, hf] at hsh
    simpa only [Option.map_some, Option.some.injEq, shp, Prod.mk.injEq] using hsh
  have hkf : rf.key = none := by
    have := hsh0.2.2
    rw [hk] at this
    cases h' : rf.key <;> simp_all
  have hrst : r.status = rf.status := h.rst z r rf hx hf hkf
  have hEE : Exposed s₂.f z rf ↔ Exposed s₂.c.st z r := by
    simp only [Exposed, h.fcor, hsh0.1, hrst]
  have hiz : s₂.inp z = none := by
    cases hip : s₂.inp z with
    | none => rfl
    | some ip =>
      obtain ⟨r', hr', hk'⟩ := h.inpKey z ip hip
      rw [hx, Option.some.injEq] at hr'
      subst hr'
      rw [hk] at hk'
      cases hk'
  have hnz : ∀ {w : Inst} {ip : TInp Tr (W ⊕ W)}, s₂.inp w = some ip → w ≠ z := by
    rintro w ip hw rfl; rw [hiz] at hw; cases hw
  have hR : ∀ w, (setRec s₂.c.st z { r with key := some k }).recs w =
      if w = z then some { r with key := some k } else s₂.c.st.recs w := by
    intro w; simp only [setRec, Function.update_apply]
  have hRf : ∀ w, (setRec s₂.f z { rf with key := some kk, status := st' }).recs w =
      if w = z then some { rf with key := some kk, status := st' } else s₂.f.recs w := by
    intro w; simp only [setRec, Function.update_apply]
  have hI : ∀ w, Function.update s₂.inp z (some ⟨.cap, tSF, Z⟩) w =
      if w = z then some ⟨.cap, tSF, Z⟩ else s₂.inp w := by
    intro w; simp only [Function.update_apply]
  exact
  { fl := rfl
    ph := rfl
    st := by rw [hst]
    lt := h.lt
    eph := h.eph
    srv := h.srv
    log := h.log
    ro := rfl
    inp := fun w => by
      by_cases hw : w = z
      · subst hw; simp [tinterp]
      · simp only [Function.update_of_ne hw]; exact h.inp w
    f := rfl
    cnt := h.cnt
    idx₁ := h.idx₁
    idx₂ := h.idx₂
    fcor := h.fcor
    rsh := fun w => by
      rw [hR, hRf]
      split_ifs
      · simp [shp, hsh0.1, hsh0.2.1]
      · exact h.rsh w
    rst := fun w rc rf' => by
      rw [hR, hRf]
      split_ifs
      · rintro - ⟨⟩ h'; cases h'
      · exact h.rst w rc rf'
    noticed := fun w hw => by
      rw [hR] at hw
      split_ifs at hw with hwz
      · subst hwz; exact h.noticed w (by rw [hx]; rfl)
      · exact h.noticed w hw
    inpKey := fun w ip hw => by
      rw [hR]
      by_cases hwz : w = z
      · subst hwz; exact ⟨_, ite_eq_left rfl, rfl⟩
      · simp only [Function.update_of_ne hwz] at hw
        rw [ite_eq_right hwz]; exact h.inpKey w ip hw
    logY := h.logY
    srvY := fun sv r' tSF' Z' cf' hr' hs hc => by
      rw [hR] at hr'
      split_ifs at hr' with hw
      · subst hw; cases hr'; exact h.srvY sv r tSF' Z' cf' hx hs hc
      · exact h.srvY sv r' tSF' Z' cf' hr' hs hc
    imp := fun w r' hr' hc => by
      rw [hR] at hr'
      split_ifs at hr' with hw
      · subst hw; cases hr'; exact h.imp w r hx hc
      · exact h.imp w r' hr' hc
    comp := fun w r' hr' hc => by
      rw [hRf] at hr'
      split_ifs at hr' with hw
      · subst hw; cases hr'
        have hE : Exposed s₂.f w rf := by
          by_contra hE; simp only [hst', hE, ite_false, reduceCtorEq] at hc
        rcases hE with h1 | h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inl h1)
        · refine Or.inr (Or.inr ⟨{ r with key := some k }, by rw [hR, ite_eq_left rfl], ?_⟩)
          change r.status = _
          rw [hrst, h1]
      · rcases h.comp w r' hr' hc with h1 | h1 | ⟨rc, h2, h3⟩
        · exact Or.inl h1
        · exact Or.inr (Or.inl h1)
        · refine Or.inr (Or.inr ⟨rc, ?_, h3⟩)
          rw [hR, ite_eq_right hw]; exact h2
    corr := fun w r' hr' hc hkey' => by
      rw [hRf] at hr'
      split_ifs at hr' with hw
      · subst hw; cases hr'
        have hE : ¬ Exposed s₂.f w rf := by
          intro hE; simp only [hst', hE, ite_true, reduceCtorEq] at hc
        simp only [Exposed, not_or, Bool.not_eq_true] at hE
        exact ⟨hE.1, hE.2.1⟩
      · have hz : (w.1, r'.peer) ≠ z := by
          intro hz
          simp [keyOf, hz, hRf] at hkey'
        have hkey'' : keyOf s₂.f (w.1, r'.peer) = none := by
          simp only [keyOf, hRf, ite_eq_right hz] at hkey'
          exact hkey'
        exact h.corr w r' hr' hc hkey''
    own := fun w ip hw => by
      simp only [hI] at hw
      split_ifs at hw with hwz
      · subst hwz
        cases hw
        refine ⟨rfl, { r with key := some k }, by rw [hR, ite_eq_left rfl], X', Ys, vk, σ, sf, htr,
          hinit, hresp⟩
      · obtain ⟨hl, r', hr', rest⟩ := h.own w ip hw
        exact ⟨hl, r', by rw [hR, ite_eq_right hwz]; exact hr', rest⟩
    keyed := fun w r' hr' hc => by
      rw [hRf] at hr'
      split_ifs at hr' with hw
      · subst hw; cases hr'
        have hE : ¬ Exposed s₂.f w rf := by
          intro hE; simp only [hst', hE, ite_true, reduceCtorEq] at hc
        obtain ⟨o, ho, hv⟩ := hkey (fun h' => hE (hEE.mpr h'))
        refine ⟨⟨.cap, tSF, Z⟩, by simp, o, ?_, hv⟩
        simp only [clientOf, hsh0.1, hsh0.2.1] at ho ⊢
        exact ho
      · obtain ⟨ip, hip, rest⟩ := h.keyed w r' hr' hc
        exact ⟨ip, by simp only [hI, ite_eq_right hw]; exact hip, rest⟩
    sym := fun p hp E hE hl => by
      rcases hro p hp with hp | ⟨hEx, hext⟩
      · obtain ⟨w, r', ip, hr', hc, hi, he⟩ := h.sym p hp E hE hl
        exact ⟨w, r', ip, by rw [hRf, ite_eq_right (hnz hi)]; exact hr', hc,
          by simp only [hI, ite_eq_right (hnz hi)]; exact hi, he⟩
      · refine ⟨z, _, ⟨.cap, tSF, Z⟩, by rw [hRf, ite_eq_left rfl], ?_, by simp, hext⟩
        simp [hst', hEE.mpr hEx]
    pair := fun w r₁ w' r₂ ip ip' hr1 hc1 hr2 hc2 hi hi' heq => by
      rw [hRf] at hr1 hr2
      simp only [hI] at hi hi'
      have hpeer : ∀ {w : Inst} {rc rf' : Rec (TKey Sec)}, s₂.c.st.recs w = some rc →
          s₂.f.recs w = some rf' → rf'.peer = rc.peer := by
        intro w rc rf' h1 h2
        have hsh := h.rsh w
        rw [h1, h2] at hsh
        simp only [Option.map_some, Option.some.injEq, shp, Prod.mk.injEq] at hsh
        exact hsh.1
      by_cases hw : w = z <;> by_cases hw' : w' = z
      · rw [ite_eq_left hw, Option.some.injEq] at hr1
        rw [ite_eq_left hw', Option.some.injEq] at hr2
        rw [← hr1] at hc1
        rw [← hr2] at hc2
        rw [hc1] at hc2
        cases hc2
      · rw [ite_eq_left hw, Option.some.injEq] at hr1 hi
        rw [ite_eq_right hw'] at hr2 hi'
        rw [← hr1] at hc1
        have hE : ¬ Exposed s₂.f z rf := by
          intro hE; simp only [hst', hE, ite_true, reduceCtorEq] at hc1
        rw [← hi] at heq
        obtain ⟨rw2, hrw2, hwz, hp2, hrole2, hin2, hre2⟩ :=
          partner_of G Sg trs hT h htr hw' hi' heq.symm
        have hp2' := hpeer hrw2 hr2
        rcases h.comp w' r₂ hr2 hc2 with h1 | h1 | ⟨rc, h2, h3⟩
        · apply hE; right; left; rw [hsh0.1]; rw [hwz] at h1; exact h1
        · apply hE; left; rw [hp2', hp2] at h1; exact h1
        · rw [hrw2, Option.some.injEq] at h2
          subst h2
          obtain ⟨hr3, tSF₃, Z₃, cf₃, hs₃, X₃, Y₃, vk₃, σ₃, sf₃, htr₃, hne₃⟩ :=
            h.imp w' rw2 hrw2 h3
          obtain ⟨cf₄, hs₄⟩ := hre2 hr3
          rw [hs₄, Option.some.injEq, Prod.mk.injEq] at hs₃
          have hri : r.role = .initiator := by
            cases hr : r.role
            · rfl
            · exact absurd (hr3.trans hr.symm) hrole2
          rw [htr₃, htr] at hs₃
          simp only [hri, ite_true] at hs₃
          obtain ⟨-, -, -, hX, -⟩ := trInj_shape trs hT hs₃.1
          apply hne₃
          rw [hwz, hp2, ← hX]
          exact hinit hri
      · rw [ite_eq_right hw] at hr1 hi
        rw [ite_eq_left hw', Option.some.injEq] at hr2 hi'
        rw [← hr2] at hc2
        have hE : Exposed s₂.f z rf := by
          by_contra hE; simp only [hst', hE, ite_false, reduceCtorEq] at hc2
        rw [← hi'] at heq
        obtain ⟨rw1, hrw1, hwz, hp1, hrole1, hin1, -⟩ := partner_of G Sg trs hT h htr hw hi heq
        have hp1' := hpeer hrw1 hr1
        have hkz : keyOf s₂.f (w.1, r₁.peer) = none := by
          rw [hp1', hp1, hwz]
          simp [keyOf, hf, hkf]
        obtain ⟨hc₁, hc₂⟩ := h.corr w r₁ hr1 hc1 hkz
        rcases hE with h1 | h1 | h1
        · rw [hp1', hp1, h1] at hc₂; cases hc₂
        · rw [hwz] at hc₁; rw [hsh0.1] at h1; rw [h1] at hc₁; cases hc₁
        · obtain ⟨hr3, tSF₃, Z₃, cf₃, hs₃, X₃, Y₃, vk₃, σ₃, sf₃, htr₃, hne₃⟩ :=
            h.imp z r hx (by rw [hrst, h1])
          obtain ⟨cf₄, hs₄⟩ := hresp hr3
          rw [hs₄, Option.some.injEq, Prod.mk.injEq] at hs₃
          rw [htr₃, htr] at hs₃
          simp only [hr3, reduceCtorEq, ite_false] at hs₃
          obtain ⟨-, -, -, hX, -⟩ := trInj_shape trs hT hs₃.1
          have hri : rw1.role = .initiator := by
            cases hr : rw1.role
            · rfl
            · exact absurd (hr.trans hr3.symm) hrole1
          apply hne₃
          rw [← hX, ← hwz]
          exact hin1 hri
      · rw [ite_eq_right hw] at hr1 hi
        rw [ite_eq_right hw'] at hr2 hi'
        exact h.pair w r₁ w' r₂ ip ip' hr1 hc1 hr2 hc2 hi hi' heq
    srvTr := fun w p hs => by
      obtain ⟨r', hr', rest⟩ := h.srvTr w p hs
      by_cases hw : w = z
      · subst hw
        rw [hx, Option.some.injEq] at hr'
        subst hr'
        exact ⟨{ r with key := some k }, by rw [hR, ite_eq_left rfl], rest⟩
      · exact ⟨r', by rw [hR, ite_eq_right hw]; exact hr', rest⟩
    ncomp := fun w r' hr' => by
      rw [hR] at hr'
      split_ifs at hr' with hw
      · cases hr'; exact h.ncomp z r hx
      · exact h.ncomp w r' hr' }

omit [DecidableEq Sec] [Inhabited Sec] in
/-- **Correctness of the symbolic key of a session**: the key derivation of the four stage
inputs on the values of the table is the image of the symbolic one. -/
theorem keysK_tinterp (x : S) (tb : List (TInp Tr (W ⊕ W) × Sec)) (z : Inst) (tSF : Tr)
    (Z : W ⊕ W) (cf : Sec) :
    keysK lazyKDF (tlsDHAlg G Sg trs) (tb.map (tinterpE G x)) z tSF (X3DHSquareGDH.ev G x Z) cf =
      (skeys G trs (ddhOracle (gapDHDef G)) (G.pub x) tb tSF Z cf).map
        fun k => (k.1, k.2.map (tinterpE G x)) := by
  simp only [keysK, skeys, lazyKDF, roAt_tinterp', PMF.bind_map, PMF.map_bind, PMF.map_comp,
    Function.comp_def]

omit [Fintype S] [DecidableEq Sec] [Inhabited Sec] in
/-- An entry of the table after the symbolic key derivation of a session is an entry before it
or one of the four stage inputs of the session. -/
theorem skeys_mem (O : W → W → W → Bool) (X : W) (tb : List (TInp Tr (W ⊕ W) × Sec)) (tSF : Tr)
    (Z : W ⊕ W) (cf : Sec) :
    ∀ k ∈ (skeys G trs O X tb tSF Z cf).support, ∀ p ∈ k.2, p ∈ tb ∨
      p.1 = ⟨.cap, tSF, Z⟩ ∨ p.1 = ⟨.sap, tSF, Z⟩ ∨ p.1 = ⟨.exp, tSF, Z⟩ ∨
        p.1 = ⟨.res, trs.trCF tSF cf, Z⟩ := by
  intro k hk p hp
  simp only [skeys, PMF.support_bind, PMF.support_map, Set.mem_iUnion, Set.mem_image] at hk
  obtain ⟨a, ha, b, hb, d, hd, e, he, rfl⟩ := hk
  rcases sro_mem G _ _ _ _ e he p hp with h4 | h4
  · rcases sro_mem G _ _ _ _ d hd p h4 with h3 | h3
    · rcases sro_mem G _ _ _ _ b hb p h3 with h2 | h2
      · rcases sro_mem G _ _ _ _ a ha p h2 with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inl h2))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h4)))

omit [DecidableEq Sec] in
/-- **The completion of a session from related states**: `deliver` of the simulator followed by
the answer of the functionality, against `deliverR`. -/
theorem red_deliver (hT : TrInj trs) {j : ℕ} {x y : S} {c : TRSt S W Tr VK SK Sec}
    {inp : Inst → Option (TInp Tr W)} {cnt : ℕ} {idx : Inst → Option ℕ}
    {s₂ : RW S W Tr VK SK Sec}
    (h : RCpl G Sg trs x y j ((((c, inp, none), s₂.f), false), cnt, idx) s₂) {z : Inst}
    {r : Rec (TKey Sec)} (hx : s₂.c.st.recs z = some r) (hk : r.key = none) {tSF : Tr}
    {Z : W ⊕ W} {X' Ys : W} {vk : VK} {σ : Sig} {sf : Sec}
    (htr : tSF = trs.trSF (trs.trCV (trs.trCert (trs.tr1 z.1
      (if r.role = .initiator then z.2 else r.peer) (if r.role = .initiator then r.peer else z.2)
      X' Ys) vk) σ) sf)
    (hinit : r.role = .initiator → shareR G (G.pub x) s₂ z = some X')
    (hresp : r.role = .responder → ∃ cf', s₂.c.srv z = some (tSF, Z, cf'))
    (hkey : ¬ Exposed s₂.c.st z r → ∃ o, s₂.c.eph (clientOf z r) = some o ∧
      (o = none → ∃ v ∈ s₂.vs, Z = .inr (G.mul (G.pub y) (G.pub v))))
    (cf : Sec) (o : TOut W VK SK Sig Sec) :
    Coupled (((deliver (tlsDHAlg G Sg trs) c inp z tSF (X3DHSquareGDH.ev G x Z) cf o).bind
        fun q => match q.2 with
          | .inl g => (PMF.uniformFintype (TKey Sec)).map fun kf =>
              (fwdOut .ack q.1.2.2 (fStepD s₂.f g kf).2, (simReset q.1, (fStepD s₂.f g kf).1))
          | .inr o => PMF.pure (.inr o, (q.1, s₂.f))).map
        fun p => (p.1, ((p.2, false), cnt, idx)))
      (deliverR G trs (ddhOracle (gapDHDef G)) (G.pub x) s₂ z tSF Z cf o) fun z₁ z₂ =>
        z₁.2.1.2 = true ∨ (z₁.1 = z₂.1 ∧ RCpl G Sg trs x y j z₁.2 z₂.2) := by
  have hst : c.st = s₂.c.st := h.st
  have hro : c.ro = s₂.c.ro.map (tinterpE G x) := h.ro
  have hc : c.st.recs z = some r := by rw [hst, hx]
  obtain ⟨rf, hf⟩ : ∃ rf, s₂.f.recs z = some rf := by
    have hsh := h.rsh z
    rw [hx] at hsh
    cases h' : s₂.f.recs z <;> simp_all
  have hkf : rf.key = none := by
    have hsh := h.rsh z
    rw [hx, hf] at hsh
    simp only [Option.map_some, Option.some.injEq, shp, Prod.mk.injEq, hk] at hsh
    cases h' : rf.key <;> simp_all
  unfold deliver deliverR
  simp only [hc, hx]
  by_cases hE : Exposed s₂.c.st z r
  · have hE' : Exposed c.st z r := by rw [hst]; exact hE
    simp only [ite_eq_left hE, ite_eq_left hE', hro, keysK_tinterp, PMF.map_comp, PMF.bind_map,
      PMF.map_bind]
    refine coupled_bind (coupled_same_supp _) ?_
    rintro k _ ⟨rfl, hk'⟩
    simp only [Function.comp_apply, fStepD, fAdvD, fwdOut, simReset, PMF.map_comp]
    refine coupled_map _ _ ((coupled_same _).mono ?_)
    rintro kf _ rfl
    refine Or.inr ⟨rfl, ?_⟩
    simp only [Function.comp_apply, setKey_of hc, setKey_of hx, Prod.mk.eta,
      X3DHSquareHops.newKeyStep_of hf hkf]
    exact rCpl_deliver G Sg trs hT h hx hf hk htr hinit hresp hkey k.1 _ _ rfl k.2
      (fun p hp => by
        rcases skeys_mem G trs _ _ _ _ _ _ k hk' p hp with hp | hp | hp | hp | hp
        · exact Or.inl hp
        all_goals
          refine Or.inr ⟨hE, ?_⟩
          rw [hp]
          have := extIn_stages (tlsDHAlg G Sg trs) tSF (X3DHSquareGDH.ev G x Z) cf
          simp only [tinterp]
          tauto)
  · have hE' : ¬ Exposed c.st z r := by rw [hst]; exact hE
    simp only [ite_eq_right hE, ite_eq_right hE', PMF.pure_bind]
    have hall : Option.all (fun i => decide (i = (⟨.cap, tSF, X3DHSquareGDH.ev G x Z⟩ : TInp Tr W)))
        (inp (z.1, r.peer)) = Option.all
          (fun i => sinpEq G (ddhOracle (gapDHDef G)) (G.pub x) i ⟨.cap, tSF, Z⟩)
          (s₂.inp (z.1, r.peer)) := by
      have hi : inp (z.1, r.peer) = (s₂.inp (z.1, r.peer)).map (tinterp G x) := h.inp _
      rw [hi]
      cases s₂.inp (z.1, r.peer) with
      | none => rfl
      | some ip => simp [sinpEq_ddh, tinterp]
    rw [PMF.map_comp, hall]
    refine coupled_map _ _ ((coupled_same _).mono ?_)
    rintro kf _ rfl
    refine Or.inr ⟨rfl, ?_⟩
    simp only [Function.comp_apply, setKey_of hc, setKey_of hx, simReset]
    split_ifs with hb
    · simp only [fStepD, fAdvD, Prod.mk.eta, X3DHSquareHops.newKeyStep_of hf hkf]
      have hR := rCpl_deliver G Sg trs hT h hx hf hk htr hinit hresp hkey default
        (newKeyVal s₂.f z rf default kf) _ rfl s₂.c.ro (fun p hp => Or.inl hp)
      rw [← hro] at hR
      exact hR
    · simp only [fStepD, fAdvD, Prod.mk.eta, X3DHSquareHops.newKeyFreshStep_of hf hkf]
      have hR := rCpl_deliver G Sg trs hT h hx hf hk htr hinit hresp hkey default
        (if Exposed s₂.f z rf then default else kf) _ rfl s₂.c.ro (fun p hp => Or.inl hp)
      rw [← hro] at hR
      exact hR

omit [Fintype S] [SampleableType W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] [Inhabited Sec] in
/-- New signing keys and new table entries at the labels `sfin` and `cfin` keep the relation. -/
theorem rCpl_lt_ro {j : ℕ} {x y : S} {c : TRSt S W Tr VK SK Sec}
    {inp : Inst → Option (TInp Tr W)} {cnt : ℕ} {idx : Inst → Option ℕ}
    {s₂ : RW S W Tr VK SK Sec}
    (h : RCpl G Sg trs x y j ((((c, inp, none), s₂.f), false), cnt, idx) s₂)
    (lt' : PartyId → Option (VK × SK)) (ro₂ : List (TInp Tr (W ⊕ W) × Sec))
    (hro : ∀ p ∈ ro₂, p ∈ s₂.c.ro ∨ p.1.lbl = .sfin ∨ p.1.lbl = .cfin) :
    RCpl G Sg trs x y j
      (((({ c with lt := lt', ro := ro₂.map (tinterpE G x) }, inp, none), s₂.f), false), cnt, idx)
      { s₂ with c := { s₂.c with lt := lt', ro := ro₂ } } :=
  { h with
    lt := rfl
    ro := rfl
    sym := fun p hp E hE hl => by
      rcases hro p hp with hp | hp | hp
      · exact h.sym p hp E hE hl
      · rcases hl with hl | hl | hl | hl <;> rw [hl] at hp <;> cases hp
      · rcases hl with hl | hl | hl | hl <;> rw [hl] at hp <;> cases hp }

/-- The step of `cliRecv` from related states. -/
theorem red_cliRecv (hT : TrInj trs) (j : ℕ) (x y : S) (s₁ : HSt S W Tr VK SK Sig Sec)
    (s₂ : RW S W Tr VK SK Sec) (sid : SessionId) (pid : PartyId) (Y' : W) (σ : Sig) (sf : Sec)
    (h : RCpl G Sg trs x y j s₁ s₂) :
    Coupled (hOx (tlsDHAlg G Sg trs) j x s₁ (.inr (.cliRecv sid pid Y' σ sf)))
      (redO G Sg trs j (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) s₂
        (.inr (.cliRecv sid pid Y' σ sf))) fun z₁ z₂ =>
        z₁.2.1.2 = true ∨ (z₁.1 = z₂.1 ∧ RCpl G Sg trs x y j z₁.2 z₂.2) := by
  obtain ⟨⟨⟨⟨c, inp, ph⟩, f⟩, fl⟩, cnt, idx⟩ := s₁
  have hph : ph = none := h.ph
  have hfl : fl = false := h.fl
  have hst : c.st = s₂.c.st := h.st
  have hlt : c.lt = s₂.c.lt := h.lt
  have hlog : c.log = s₂.c.log := h.log
  have hro : c.ro = s₂.c.ro.map (tinterpE G x) := h.ro
  have hf : f = s₂.f := h.f
  subst hph hfl hf
  have heph : ∀ w, c.eph w = (s₂.c.eph w).map fun o => o.getD x := h.eph
  change Coupled (hO _ _ _) _ _
  rw [hO_nh G Sg trs _ _ (fun _ _ h => by cases h) (fun _ _ => rfl), simO_core]
  simp only [simCore, redO, cliRecvR, cliCheckK]
  cases hx : s₂.c.st.recs (sid, pid) with
  | none =>
    have hc : c.st.recs (sid, pid) = none := by rw [hst, hx]
    simp only [hc, PMF.pure_bind, PMF.pure_map]
    exact coupled_pure (Or.inr ⟨rfl, h⟩)
  | some r =>
    have hc : c.st.recs (sid, pid) = some r := by rw [hst, hx]
    cases he : s₂.c.eph (sid, pid) with
    | none =>
      have hce : c.eph (sid, pid) = none := by rw [heph, he]; rfl
      simp only [hc, hce, PMF.pure_bind, PMF.pure_map]
      exact coupled_pure (Or.inr ⟨rfl, h⟩)
    | some o =>
      have hce : c.eph (sid, pid) = some (o.getD x) := by rw [heph, he]; rfl
      by_cases hcond : r.role = .initiator ∧ r.key.isNone = true
      swap
      · simp only [hc, hce, ite_eq_right hcond, PMF.pure_bind, PMF.pure_map]
        exact coupled_pure (Or.inr ⟨rfl, h⟩)
      simp only [hc, hce, ite_eq_left hcond, ltAt_eq, rlt_eq, hlt, PMF.bind_map, PMF.bind_bind,
        PMF.map_bind]
      refine coupled_bind (coupled_same _) ?_
      rintro l _ rfl
      have hk : r.key = none := Option.isNone_iff_eq_none.mp hcond.2
      have hcl : clientOf (sid, pid) r = (sid, pid) := by simp [clientOf, hcond.1]
      have hro2 : ∀ (sv cf : Sec × List (TInp Tr (W ⊕ W) × Sec)) (i₁ i₂ : TInp Tr (W ⊕ W)),
          i₁.lbl = .sfin → i₂.lbl = .cfin →
          sv ∈ (sro G (ddhOracle (gapDHDef G)) (G.pub x) s₂.c.ro i₁).support →
          cf ∈ (sro G (ddhOracle (gapDHDef G)) (G.pub x) sv.2 i₂).support →
          (∀ p ∈ sv.2, p ∈ s₂.c.ro ∨ p.1.lbl = .sfin ∨ p.1.lbl = .cfin) ∧
          (∀ p ∈ cf.2, p ∈ s₂.c.ro ∨ p.1.lbl = .sfin ∨ p.1.lbl = .cfin) := by
        intro sv cf i₁ i₂ h₁ h₂ hsv hcf
        have h3 : ∀ p ∈ sv.2, p ∈ s₂.c.ro ∨ p.1.lbl = .sfin ∨ p.1.lbl = .cfin := by
          intro p hp
          rcases sro_mem G _ _ _ _ sv hsv p hp with hp | hp
          · exact Or.inl hp
          · exact Or.inr (Or.inl (by rw [hp, h₁]))
        refine ⟨h3, fun p hp => ?_⟩
        rcases sro_mem G _ _ _ _ cf hcf p hp with hp | hp
        · exact h3 p hp
        · exact Or.inr (Or.inr (by rw [hp, h₂]))
      have hro1 : ∀ (sv : Sec × List (TInp Tr (W ⊕ W) × Sec)) (i₁ : TInp Tr (W ⊕ W)),
          i₁.lbl = .sfin →
          sv ∈ (sro G (ddhOracle (gapDHDef G)) (G.pub x) s₂.c.ro i₁).support →
          ∀ p ∈ sv.2, p ∈ s₂.c.ro ∨ p.1.lbl = .sfin ∨ p.1.lbl = .cfin := by
        intro sv i₁ h₁ hsv p hp
        rcases sro_mem G _ _ _ _ sv hsv p hp with hp | hp
        · exact Or.inl hp
        · exact Or.inr (Or.inl (by rw [hp, h₁]))
      simp only [Function.comp_apply, lazyKDF]
      rcases o with _ | xs
      · simp only [Option.getD_none]
        rw [show G.exp Y' x = X3DHSquareGDH.ev G x (.inr Y') from rfl]
        simp only [hro, roAt_tinterp', PMF.bind_map, PMF.bind_bind]
        refine coupled_bind (coupled_same_supp _) ?_
        rintro sv _ ⟨rfl, hsv⟩
        simp only [Function.comp_apply]
        split_ifs with hv1 hv2 hv2
        · simp only [roAt_tinterp', PMF.bind_map]
          refine coupled_bind (coupled_same_supp _) ?_
          rintro cf _ ⟨rfl, hcf⟩
          simp only [Function.comp_apply]
          have h' := rCpl_lt_ro G Sg trs h (Function.update s₂.c.lt r.peer (some l)) cf.2
            (hro2 sv cf _ _ rfl rfl hsv hcf).2
          rw [← PMF.map_bind]
          refine red_deliver G Sg trs hT h' (z := (sid, pid))
            (s₂ := { s₂ with
              c := { s₂.c with
                lt := Function.update s₂.c.lt r.peer (some l)
                ro := cf.2 } }) hx hk (Z := .inr Y') (X' := G.pub x) (Ys := Y')
            (vk := l.1) (σ := σ) (sf := sf) (by rw [ite_eq_left hcond.1, ite_eq_left hcond.1])
            (fun _ => by simp [shareR, he]) (fun hr => absurd (hcond.1.symm.trans hr) (by simp))
            ?_ cf.1 _
          intro hE
          refine ⟨none, by rw [hcl]; exact he, fun _ => ?_⟩
          have hcor : s₂.c.st.corrupt r.peer = false := by
            cases hcp : s₂.c.st.corrupt r.peer
            · rfl
            · exact absurd (Or.inr (Or.inl hcp)) hE
          obtain ⟨-, -, hlg⟩ := hv2
          simp only [hcor, Bool.false_or, decide_eq_true_eq] at hlg
          obtain ⟨a, b, d, X'', Ys', vk', htC, himp⟩ := h.logY _ _ hlg
          obtain ⟨h1, -⟩ := hT.2.1 _ _ _ _ htC
          obtain ⟨-, -, -, hX, hY⟩ := hT.1 _ _ _ _ _ _ _ _ _ _ h1
          obtain ⟨v, hv, hYs⟩ := himp hX.symm
          exact ⟨v, hv, by rw [hY, hYs]⟩
        · exact absurd (by rw [hst, hlog] at hv1; simpa using hv1) hv2
        · exact absurd (by rw [← hst, ← hlog] at hv2; simpa using hv2) hv1
        · simp only [PMF.pure_bind, PMF.pure_map]
          exact coupled_pure (Or.inr ⟨rfl, rCpl_lt_ro G Sg trs h _ sv.2 (hro1 sv _ rfl hsv)⟩)
      · simp only [Option.getD_some]
        simp only [hro, roAt_tinterp_inl, PMF.bind_map, PMF.bind_bind]
        refine coupled_bind (coupled_same_supp _) ?_
        rintro sv _ ⟨rfl, hsv⟩
        simp only [Function.comp_apply]
        split_ifs with hv1 hv2 hv2
        · simp only [roAt_tinterp_inl, PMF.bind_map]
          refine coupled_bind (coupled_same_supp _) ?_
          rintro cf _ ⟨rfl, hcf⟩
          simp only [Function.comp_apply]
          have h' := rCpl_lt_ro G Sg trs h (Function.update s₂.c.lt r.peer (some l)) cf.2
            (hro2 sv cf _ _ rfl rfl hsv hcf).2
          rw [← PMF.map_bind]
          exact red_deliver G Sg trs hT h' (z := (sid, pid))
            (s₂ := { s₂ with
              c := { s₂.c with
                lt := Function.update s₂.c.lt r.peer (some l)
                ro := cf.2 } }) hx hk (Z := .inl (G.exp Y' xs)) (X' := G.pub xs) (Ys := Y')
            (vk := l.1) (σ := σ) (sf := sf) (by rw [ite_eq_left hcond.1, ite_eq_left hcond.1])
            (fun _ => by simp [shareR, he]) (fun hr => absurd (hcond.1.symm.trans hr) (by simp))
            (fun _ => ⟨some xs, by rw [hcl]; exact he, fun h' => by cases h'⟩) cf.1 _
        · exact absurd (by rw [hst, hlog] at hv1; simpa using hv1) hv2
        · exact absurd (by rw [← hst, ← hlog] at hv2; simpa using hv2) hv1
        · simp only [PMF.pure_bind, PMF.pure_map]
          exact coupled_pure (Or.inr ⟨rfl, rCpl_lt_ro G Sg trs h _ sv.2 (hro1 sv _ rfl hsv)⟩)

/-- The step of `srvFin` from related states. -/
theorem red_srvFin (hT : TrInj trs) (j : ℕ) (x y : S) (s₁ : HSt S W Tr VK SK Sig Sec)
    (s₂ : RW S W Tr VK SK Sec) (sid : SessionId) (pid : PartyId) (cfin : Sec)
    (h : RCpl G Sg trs x y j s₁ s₂) :
    Coupled (hOx (tlsDHAlg G Sg trs) j x s₁ (.inr (.srvFin sid pid cfin)))
      (redO G Sg trs j (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) s₂
        (.inr (.srvFin sid pid cfin))) fun z₁ z₂ =>
        z₁.2.1.2 = true ∨ (z₁.1 = z₂.1 ∧ RCpl G Sg trs x y j z₁.2 z₂.2) := by
  obtain ⟨⟨⟨⟨c, inp, ph⟩, f⟩, fl⟩, cnt, idx⟩ := s₁
  have hph : ph = none := h.ph
  have hfl : fl = false := h.fl
  have hst : c.st = s₂.c.st := h.st
  have hf : f = s₂.f := h.f
  subst hph hfl hf
  have hsrv : ∀ w, c.srv w =
      (s₂.c.srv w).map fun p => (p.1, X3DHSquareGDH.ev G x p.2.1, p.2.2) := h.srv
  have hF : srvFinCheck c (sid, pid) cfin = (srvFinCheck s₂.c (sid, pid) cfin).map
      fun p => (p.1, X3DHSquareGDH.ev G x p.2.1, p.2.2) := by
    unfold srvFinCheck
    rw [hst, hsrv]
    cases s₂.c.st.recs (sid, pid) <;> cases s₂.c.srv (sid, pid) <;> simp only [Option.map_none,
      Option.map_some]
    split_ifs <;> rfl
  change Coupled (hO _ _ _) _ _
  rw [hO_nh G Sg trs _ _ (fun _ _ h => by cases h) (fun _ _ => rfl), simO_core]
  simp only [simCore, redO, hF]
  cases hsf : srvFinCheck s₂.c (sid, pid) cfin with
  | none =>
    simp only [Option.map_none, PMF.pure_bind, PMF.pure_map]
    exact coupled_pure (Or.inr ⟨rfl, h⟩)
  | some p =>
    obtain ⟨tSF, Z, cfp⟩ := p
    obtain ⟨r, hr, hk, hs⟩ : ∃ r, s₂.c.st.recs (sid, pid) = some r ∧ r.key = none ∧
        s₂.c.srv (sid, pid) = some (tSF, Z, cfp) := by
      unfold srvFinCheck at hsf
      split at hsf
      · rename_i r q h1 h2
        split_ifs at hsf with hc
        cases hsf
        exact ⟨r, h1, Option.isNone_iff_eq_none.mp hc.2.1, h2⟩
      · cases hsf
    obtain ⟨r', hr', hrole, X', Ys, vk, σ, sf, htr⟩ := h.srvTr (sid, pid) _ hs
    rw [hr, Option.some.injEq] at hr'
    subst hr'
    simp only [Option.map_some]
    refine red_deliver G Sg trs hT h hr hk (X' := X') (Ys := Ys) (vk := vk) (σ := σ) (sf := sf)
      (by simp only [hrole, reduceCtorEq, ite_false]; exact htr)
      (fun hi => absurd (hi.symm.trans hrole) (by simp)) (fun _ => ⟨cfp, hs⟩) ?_ cfp .ack
    intro hE
    have hnc : r.status ≠ .compromised := fun hc => hE (Or.inr (Or.inr hc))
    obtain ⟨o, ho, hv⟩ := h.srvY (sid, pid) r tSF Z cfp hr hs hnc
    refine ⟨o, ?_, hv⟩
    simp only [clientOf, hrole, reduceCtorEq, ite_false]
    exact ho

/-- **A step of the two worlds from related states**: the first world reaches a collision, or the
answers agree and the states stay related. -/
theorem red_step (hT : TrInj trs) (j : ℕ) (x y : S) (s₁ : HSt S W Tr VK SK Sig Sec)
    (s₂ : RW S W Tr VK SK Sec) (d : TOEv W Tr Sig Sec) (h : RCpl G Sg trs x y j s₁ s₂) :
    Coupled (hOx (tlsDHAlg G Sg trs) j x s₁ d)
      (redO G Sg trs j (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) s₂ d) fun z₁ z₂ =>
        z₁.2.1.2 = true ∨ (z₁.1 = z₂.1 ∧ RCpl G Sg trs x y j z₁.2 z₂.2) := by
  rcases d with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) |
    (_ | _ | pid | pid | ⟨sid, pid⟩ | ⟨sid, pid, X'⟩ | ⟨sid, pid, Y', σ, sf⟩ | ⟨sid, pid, cfin⟩ |
      w)
  · exact red_newSession G Sg trs j x y s₁ s₂ sid pid peer role h
  · exact red_getKey G Sg trs j x y s₁ s₂ sid pid h
  · exact red_idle G Sg trs j x y s₁ s₂ h
  · exact red_poll G Sg trs j x y s₁ s₂ h
  · exact red_pub G Sg trs j x y s₁ s₂ pid h
  · exact red_corrupt G Sg trs j x y s₁ s₂ pid h
  · exact red_hello G Sg trs j x y s₁ s₂ sid pid h
  · exact red_srvRecv G Sg trs j x y s₁ s₂ sid pid X' h
  · exact red_cliRecv G Sg trs hT j x y s₁ s₂ sid pid Y' σ sf h
  · exact red_srvFin G Sg trs hT j x y s₁ s₂ sid pid cfin h
  · exact red_kdf G Sg trs j x y s₁ s₂ w h

/-- **The coupling of the world with the `j`-th client share fixed and the world of the
reduction.** For injective transcript operations and the challenge exponents `x`, `y`, there is a
relation between the states of `hOx j x` and of the world of the reduction for the `j`-th share
on `(g^x, g^y)` with the decision oracle of the group, holding at the initial states, such that
each step from related states is coupled so that the first world reaches a collision, or the
second reaches the extraction event, or the answers agree, the states are related and
`KeyHitJ j` fails. The server exponent `y_s` of a server session that receives `g^x` is coupled
with the rerandomisation exponent `v` by `y_s = y + v`, and a symbolic value `inr E` stands for
`E^x`. -/
theorem red_coupling (hT : TrInj trs) (j : ℕ) (x y : S) :
    ∃ I : HSt S W Tr VK SK Sig Sec → RW S W Tr VK SK Sec → Prop,
      I (hInit (tlsDHAlg G Sg trs)) rwInit ∧
      ∀ s₁ s₂ d, I s₁ s₂ → Coupled (hOx (tlsDHAlg G Sg trs) j x s₁ d)
        (redO G Sg trs j (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) s₂ d) fun z₁ z₂ =>
          z₁.2.1.2 = true ∨ RGood G x y z₂.2 ∨
            (z₁.1 = z₂.1 ∧ I z₁.2 z₂.2 ∧ ¬ KeyHitJ (tlsDHAlg G Sg trs) j z₁.2) := by
  refine ⟨RCpl G Sg trs x y j, rCpl_init G Sg trs x y j, fun s₁ s₂ d h => ?_⟩
  refine (red_step G Sg trs hT j x y s₁ s₂ d h).mono fun z₁ z₂ hz => ?_
  rcases hz with hf | ⟨he, hI⟩
  · exact Or.inl hf
  · by_cases hk : KeyHitJ (tlsDHAlg G Sg trs) j z₁.2
    · exact Or.inr (Or.inl (rgood_of_keyHitJ G Sg trs hT hI hk))
    · exact Or.inr (Or.inr ⟨he, hI, hk⟩)

open Classical in
/-- **The world with the `j`-th client share fixed, against the world of the reduction.** For
injective transcript operations and the challenge exponents `x`, `y`, the flag of `KeyHitJ j` in
`hOx j x` is set at most with the probability that the reduction for the `j`-th share, on
`(g^x, g^y)` with the decision oracle of the group, outputs `g^{xy}`. -/
theorem keyHitJ_le_red (hT : TrInj trs) (j : ℕ) (x y : S)
    (B : OracleAdv (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) Bool) :
    (OracleAdv.run (OracleAdv.flagWhen (fun _ _ z => KeyHitJ (tlsDHAlg G Sg trs) j z.2)
      (hOx (tlsDHAlg G Sg trs) j x)) B (hInit (tlsDHAlg G Sg trs), false)).toOuterMeasure
        {z | z.2.2 = true} ≤
      ((tlsGdhOut G Sg trs j (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) B).map
        fun c => decide (c = G.pub (x * y))) true := by
  obtain ⟨I, hI0, hc⟩ := red_coupling G Sg trs hT j x y
  have hdead : ∀ (a : HSt S W Tr VK SK Sig Sec) d, a.1.2 = true →
      ∀ z ∈ (hOx (tlsDHAlg G Sg trs) j x a d).support, z.2.1.2 = true := by
    have hOd : ∀ (a : HSt S W Tr VK SK Sig Sec) d, a.1.2 = true →
        ∀ z ∈ (hO (tlsDHAlg G Sg trs) a d).support, z.2.1.2 = true := by
      intro a d ha z hz
      simp only [hO, PMF.support_map, Set.mem_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      simp only [collO, OracleAdv.flagWhen, PMF.support_map, Set.mem_image] at hw
      obtain ⟨u, -, rfl⟩ := hw
      simp [ha]
    intro a d ha z hz
    unfold hOx at hz
    split at hz
    · split_ifs at hz
      · rw [PMF.support_pure, Set.mem_singleton_iff] at hz
        subst hz
        simp [helloRes, ha]
      · exact hOd a _ ha z hz
    · exact hOd a d ha z hz
  have h := flag_le_final_of_coupled (hOx (tlsDHAlg G Sg trs) j x)
    (redO G Sg trs j (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y))
    (KeyHitJ (tlsDHAlg G Sg trs) j) (fun a => a.1.2 = true) (RGood G x y) I hdead
    (fun a ha hk => by rw [hk.1] at ha; cases ha)
    (fun s d hs z hz => hs.mono G (redO_mono G Sg trs j _ _ _ s d z hz)) hc B _ _ hI0
  refine h.trans ?_
  rw [tlsGdhOut, PMF.map_comp, ← PMF.toOuterMeasure_apply_singleton,
    PMF.toOuterMeasure_map_apply]
  refine PMF.toOuterMeasure_mono _ fun z hz => ?_
  simp only [Set.mem_preimage, Function.comp_apply, Set.mem_singleton_iff, decide_eq_true_eq]
  exact extractT_of_good G hz.1

open Classical in
/-- **The `j`-th client share under gap Diffie–Hellman**: the flag of `KeyHitJ j` in the
simulated world is set at most with the advantage of the reduction for the `j`-th share. -/
theorem keyHitJ_le_gapDH (hT : TrInj trs) (j : ℕ)
    (B : OracleAdv (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) Bool) :
    (OracleAdv.run (OracleAdv.flagWhen (fun _ _ z => KeyHitJ (tlsDHAlg G Sg trs) j z.2)
      (hO (tlsDHAlg G Sg trs))) B (hInit (tlsDHAlg G Sg trs), false)).toOuterMeasure
        {z | z.2.2 = true} ≤ GapDH_Advantage (gapDHDef G) (tlsGdhRed G Sg trs j B) := by
  rw [keyHitJ_eager, gapDH_advantage_tlsGdhRed, PMF.bind_apply]
  refine ENNReal.tsum_le_tsum fun x => ?_
  gcongr
  rw [PMF.bind_apply]
  calc _ = ∑' y : S, PMF.uniformFintype S y * (OracleAdv.run (OracleAdv.flagWhen
        (fun _ _ z => KeyHitJ (tlsDHAlg G Sg trs) j z.2) (hOx (tlsDHAlg G Sg trs) j x)) B
          (hInit (tlsDHAlg G Sg trs), false)).toOuterMeasure {z | z.2.2 = true} := by
        simp only [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ ≤ _ := ENNReal.tsum_le_tsum fun y => by
        gcongr
        exact keyHitJ_le_red G Sg trs hT j x y B

/-- **A query at the key of a fresh session under gap Diffie–Hellman.** For injective transcript
operations and an oracle adversary `B` with at most `n` queries, the probability of `KeyHit` in
the simulated world is at most the gap Diffie–Hellman bound. -/
theorem keyProb_le_gapDH (hT : TrInj trs) (n : ℕ)
    (B : OracleAdv (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) Bool) (hB : B.IsQueryBound n) :
    keyProb (tlsDHAlg G Sg trs) B ≤ tlsGdhBound G Sg trs n B :=
  (keyProb_le_sum _ n B hB).trans
    (Finset.sum_le_sum fun j _ => keyHitJ_le_gapDH G Sg trs hT j B)

/-- **The collision of a client share.** For injective transcript operations and an oracle
adversary `B` with at most `n` queries, the probability of `CollAt` in the simulated world is at
most `n * n / |S|`. -/
theorem collProb_le (hT : TrInj trs) (n : ℕ)
    (B : OracleAdv (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) Bool) (hB : B.IsQueryBound n) :
    collProb (tlsDHAlg G Sg trs) B ≤ tlsCollBound S n := by
  classical
  have hinit : (simInit (tlsDHAlg G Sg trs)).2 = initSt := rfl
  have h := run_flagWhen_le_count (simO (tlsDHAlg G Sg trs)) (CollAt (tlsDHAlg G Sg trs))
    (fun t => RecNoticed t.2) (fun t => t.2.notices.length) (Fintype.card S : ℝ≥0∞)⁻¹
    (fun s d hs x hx => by
      rcases simO_f _ s d x hx with h | ⟨g, kf, h⟩
      · exact ⟨by rw [h]; exact hs, by rw [h]; omega⟩
      · rw [h]
        exact ⟨(fStepD_frame s.2 g kf hs).2, (fStepD_frame s.2 g kf hs).1⟩)
    (fun s d hs => collAt_step_le G Sg trs hT s d hs) B n n hB (simInit (tlsDHAlg G Sg trs))
    (fun y hy => by simp [hinit, initSt] at hy) (by simp [hinit, initSt])
  unfold collProb tlsCollBound
  rw [OracleAdv.run_flagWhen_inst _ (CollAt _) _ (fun _ _ _ => Classical.propDecidable _)] at h
  refine h.trans (le_of_eq ?_)
  rw [div_eq_mul_inv, mul_assoc]

/-- **The bad event under gap Diffie–Hellman.** For transcript operations that are injective and
an oracle adversary `B` with at most `n` queries, the probability of the bad event is at most the
gap Diffie–Hellman advantages of the reductions `tlsGdhRed G Sg trs i B`, `i < n`, plus the
collision bound. -/
theorem badGame_le_gapDH (hT : TrInj trs) (n : ℕ)
    (B : OracleAdv (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) Bool) (hB : B.IsQueryBound n) :
    badProb (tlsDHAlg G Sg trs) B ≤ tlsGdhBound G Sg trs n B + tlsCollBound S n :=
  (badProb_le _ B).trans (add_le_add (keyProb_le_gapDH G Sg trs hT n B hB)
    (collProb_le G Sg trs hT n B hB))

/-- **The filtered TLS protocol realizes `F_AKEImp … srvImp` behind `tlsSim` under gap
Diffie–Hellman.** Ideal functionality: `F_AKEImp (SPComp.sample (TKey Sec)) srvImp true`,
unilaterally authenticated key exchange with uniform four-component keys. Real world: the
filtered protocol over the group `G`. Simulator: `tlsSim`. For injective transcript operations and
every environment `Z`, the distance is at most the gap Diffie–Hellman bound of the oracle
reduction of `Z`, which makes `Z.input.rounds` queries, plus the collision bound. -/
theorem tls_filt_realizesSim_gapDH (hT : TrInj trs) :
    RealizesSim (tlsFiltOfK (lazyKDF (D := TInp Tr W) (K := Sec)) (tlsDHAlg G Sg trs))
      (F_AKEImp (SPComp.sample (TKey Sec)) srvImp true) (tlsSim (tlsDHAlg G Sg trs))
      (fun _ Z => tlsGdhBound G Sg trs Z.input.rounds
          ((OProt.oracle (Q := TOEv W Tr Sig Sec) (A := TOOut W VK SK Sig Sec)).reduction Z) +
        tlsCollBound S Z.input.rounds) :=
  fun ζ Z => (tls_filt_realizesSim_oracleGame (tlsDHAlg G Sg trs) ζ Z).trans
    ((filt_advantage_le_badGame G Sg trs hT _).trans
      (badGame_le_gapDH G Sg trs hT _ _ (OProt.isQueryBound_oracle_reduction Z)))

/-- **TLS 1.3 realizes the unilaterally authenticated key exchange behind `tlsSim`.** Ideal
functionality: `F_AKEImp (SPComp.sample (TKey Sec)) srvImp true`. Real world: the real protocol
`tlsRealOf (tlsDHAlg G Sg trs)`, signed ephemeral Diffie–Hellman over `G` with key confirmation.
Simulator: `tlsSim`. For injective transcript operations, every finite set of servers `P` and
every environment `Z`, the distance is at most the EUF-CMA bound `tlsSigBound` plus the gap
Diffie–Hellman bound `tlsGdhBound` of the oracle reduction of `Z` plus the collision bound. -/
theorem tls_realizesSim_gapDH (hT : TrInj trs) (P : Finset PartyId) :
    RealizesSim (tlsRealOf (tlsDHAlg G Sg trs))
      (F_AKEImp (SPComp.sample (TKey Sec)) srvImp true) (tlsSim (tlsDHAlg G Sg trs))
      (fun _ Z =>
        tlsSigBound (tlsDHAlg G Sg trs) P
          ((OProt.oracle (Q := TOEv W Tr Sig Sec) (A := TOOut W VK SK Sig Sec)).reduction Z) +
        tlsGdhBound G Sg trs Z.input.rounds
          ((OProt.oracle (Q := TOEv W Tr Sig Sec) (A := TOOut W VK SK Sig Sec)).reduction Z) +
        tlsCollBound S Z.input.rounds) :=
  fun ζ Z => (TLSSquareSigned.tls_realizesSim_oracleGame (tlsDHAlg G Sg trs) P ζ Z).trans
    (by
      dsimp only
      rw [add_assoc]
      gcongr
      exact (filt_advantage_le_badGame G Sg trs hT _).trans
        (badGame_le_gapDH G Sg trs hT _ _ (OProt.isQueryBound_oracle_reduction Z)))

end Bounds

end CatCrypt.Crypto.AKE.TLSSquareGDH
