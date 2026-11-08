/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SignalStackUC
public import CatCryptCore.Crypto.Messaging.SMMultiChallenge
public import CatCryptCore.Crypto.ForkingLemma
import CatCryptCore.Tactics.DeriveTimed

/-!
# The Signal stack realizes secure messaging with corruption

The Signal stack runs X3DH and keys a secure-messaging scheme with the session key of X3DH. This
module proves that the stack realizes a secure-messaging functionality with forward secrecy and
post-compromise security windows, in the sense of Canetti, Jain, Swanberg and Varia (TCC 2022),
behind a simulator. The statement is over the record `SMScheme` of
`CatCryptCore.Crypto.Messaging.SMScheme`, so that a scheme that simulates another one
(`SMScheme.Sim`) has the bound with the advantages of the simulated scheme
(`signal_stack_realizes_FSM_sim`).

**The session.** A scheme `M : SMScheme Sst Pub Rand Wd Ct Leak` is keyed by the session key
through a keyed initialisation `ini : K → SPComp (Pub × Sst × Sst)` with
`M.init = SPComp.bind (SPComp.sample K) ini`. The schedule `Sch` of a session is an oracle tree
over the interface of the corruption games of `SMScheme`: it opens epochs, delivers them, sends
messages, asks challenge messages and corrupts the parties, and returns a view of type `V`. The
session view `smSessView M ini Sch t n ΔFS ΔPCS mode k` runs the schedule against the oracle
`smMultiOracle` of the multi-challenge game of `SMMultiChallenge`, keyed by `k`: the challenge
messages of the epoch `t`, at most `n` of them, have the ideal ciphertext `M.idealCt` when `mode`
holds at their index and the real ciphertext otherwise; a corruption answers the state of the
party exactly in the windows that `ckaAllowCorr ΔFS ΔPCS t` opens, that is outside the
`ΔFS` epochs of forward secrecy before and the `ΔPCS` epochs of post-compromise security after
the challenge epoch.

**The ideal functionality.** `F_SM M ini Sch t n ΔFS ΔPCS` is the secure channel `F_SC` of
`SignalStackUC` with the views of the sessions: for a session that completed without exposure,
the ideal view `smIdealView` (ideal ciphertexts for the challenge messages of the honest
epoch, the states that the corruption windows expose under a fresh key); for an exposed session,
the real view `smRealView k` under the adversary key `k`.

**The real world.** `(x3dhReal G).seq (smCorruptLayer M ini Sch t n ΔFS ΔPCS)`: X3DH, and the
ratchet layer, which runs the schedule against the oracles of the scheme keyed by the session key
of every `getKey` answer.

**The simulator.** `scSim G` of `SignalStackUC`, the X3DH simulator over `F_SC`, at the views of
type `V`. Its time certificate is `scSim.timeBound_timed` of `SignalStackUCTimed`.

**The bound.** The composition `stack_realizes_FSC_of` bounds the distance by the gap
Diffie–Hellman bound of X3DH and, for each key `i` of the run, the advantage of `hopRed i Z`
between the real game (a uniform key, then the real view) and the ideal view, and the probability
that the key `i` is read twice. That advantage is the multi-challenge advantage of the adversary
`smHopAdv Sch t (hopRed i Z)`, which runs the schedule and outputs the bit of `hopRed i Z` on the
view (`advantageA_eq_multiAdvantage`), and the hybrid argument of `SMMultiChallenge` bounds it
by the single-challenge corruption advantages of the reductions `smHopRed i j Z`.

## Main definitions

* `smSessView`, `smRealView`, `smIdealView`: the views of a session.
* `F_SM`: the ideal secure-messaging functionality.
* `smCorruptLayer`: the ratchet layer of the real stack.
* `smHopAdv`, `smHopRed`: the adversaries of the multi-challenge and of the corruption game.
* `fsmBound`: the bound of the Signal stack.
* `acdIni`: the keyed initialisation of the ACD construction.

## Main results

* `advantageA_eq_multiAdvantage`: the advantage of a distinguisher of the views is a
  multi-challenge advantage.
* `signal_stack_realizes_FSM`: the Signal stack realizes `F_SM` behind `scSim G`.
* `signal_stack_realizes_FSM_acd`: the same for the ACD construction `acdSM`.
* `signal_stack_realizes_FSM_sim`: the same for a scheme that simulates another one, with the
  corruption advantages of the simulated scheme.
* `smHopPlay.timed`, `smHopPlay.erase_timed` (derived), `smHopPlay.timeBound_timed`,
  `smHopRed.timeBound_timed`: the costed reductions, their erasure and their time.

## References

* R. Canetti, P. Jain, M. Swanberg, M. Varia, *Universally composable end-to-end secure
  messaging*, CRYPTO 2022.
* J. Alwen, S. Coretti, Y. Dodis, *The double ratchet: security notions, proofs, and
  modularization for the Signal protocol*, Eurocrypt 2019.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Messaging.SignalStackSM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Messaging
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.AKE.X3DHSquare CatCrypt.Crypto.AKE.X3DHSquareGDH
open CatCrypt.Crypto.Messaging.SignalStack CatCrypt.Crypto.Messaging.SignalStackUC
open CatCrypt.Crypto.PAKE.CPaceSquare (PureNF pureNF_sample)
open CatCrypt.Crypto.PAKE.DHExtract
open scoped ENNReal

/-! ## Acceptance probabilities -/

/-- Two continuations with the same acceptance probability from every heap give binds with the
same acceptance probability. -/
theorem prTrue_bind_congr {α : Type} (c : SPComp α) {f g : α → SPComp Bool}
    (hfg : ∀ a h, prTrue (f a) h = prTrue (g a) h) (h₀ : Heap) :
    prTrue (SPComp.bind c f) h₀ = prTrue (SPComp.bind c g) h₀ := by
  rw [ForkingLemma.prTrue_bind_eq_weighted, ForkingLemma.prTrue_bind_eq_weighted]
  refine tsum_congr fun p => ?_
  rcases p with _ | ⟨a, h⟩
  · rfl
  · simp only [hfg]

/-- A lifted distribution followed by a distinguisher that does not read the heap outputs `true`,
from every heap, with the probability that the output bit of the distinguisher on a sample is
`true`. -/
theorem prTrue_liftPMF_bind_of_const {α : Type} (p : PMF α) (D : α → SPComp Bool)
    (hD : ∀ a h, D a h = D a Heap.empty) (h : Heap) :
    prTrue ((liftPMF p).bind D) h = (p.bind (outBool D)) true := by
  have h1 : SPComp.bind (liftPMF p) D h = SPComp.bind (liftPMF p) D Heap.empty := by
    rw [liftPMF_bind_apply, liftPMF_bind_apply]
    simp only [hD]
  have h2 := prTrue_liftPMF_bind p D
  unfold prTrue at h2 ⊢
  rw [h1]
  exact h2

/-! ## The views of a session -/

section View

variable {K Sst Pub Rand Wd Ct Leak V : Type} [Fintype Rand] [Nonempty Rand]

/-- **The view of a session** keyed by `k`: the keyed initialisation `ini k`, and the run of the
schedule `Sch` on the public value of the initialisation against the oracle of the
multi-challenge game over `M` with the challenge epoch `t`, at most `n` challenges, the windows
`ΔFS`, `ΔPCS` and the challenge mode `mode`. -/
noncomputable def smSessView (M : SMScheme Sst Pub Rand Wd Ct Leak)
    (ini : K → SPComp (Pub × Sst × Sst))
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (t n ΔFS ΔPCS : ℕ)
    (mode : ℕ → Bool) (k : K) : SPComp V :=
  SPComp.bind (ini k) fun i =>
    liftPMF ((OracleAdv.run (smMultiOracle M ΔFS ΔPCS t n mode) (Sch i.1)
      (SMSchemeSt.init i, 0)).map Prod.fst)

/-- **The real view of a session** keyed by `k`: every challenge with the real ciphertext. -/
noncomputable def smRealView (M : SMScheme Sst Pub Rand Wd Ct Leak)
    (ini : K → SPComp (Pub × Sst × Sst))
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (t n ΔFS ΔPCS : ℕ)
    (k : K) : SPComp V :=
  smSessView M ini Sch t n ΔFS ΔPCS (fun _ => false) k

/-- **The ideal view of a session**: a fresh uniform key, and every challenge with the ideal
ciphertext. -/
noncomputable def smIdealView [Fintype K] [Nonempty K] (M : SMScheme Sst Pub Rand Wd Ct Leak)
    (ini : K → SPComp (Pub × Sst × Sst))
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (t n ΔFS ΔPCS : ℕ) :
    SPComp V :=
  SPComp.bind (SPComp.sample K) (smSessView M ini Sch t n ΔFS ΔPCS (fun _ => true))

/-- A session view of a keyed initialisation that neither touches the heap nor fails neither
touches the heap nor fails. -/
theorem smSessView_pureNF {M : SMScheme Sst Pub Rand Wd Ct Leak}
    {ini : K → SPComp (Pub × Sst × Sst)} (hini : ∀ k, PureNF (ini k))
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (t n ΔFS ΔPCS : ℕ)
    (mode : ℕ → Bool) (k : K) :
    PureNF (smSessView M ini Sch t n ΔFS ΔPCS mode k) :=
  (hini k).bind fun _ => ⟨liftPMF_isPure _, liftPMF_noFail _⟩

/-- The ideal view of a keyed initialisation that neither touches the heap nor fails neither
touches the heap nor fails. -/
theorem smIdealView_pureNF [Fintype K] [Nonempty K] {M : SMScheme Sst Pub Rand Wd Ct Leak}
    {ini : K → SPComp (Pub × Sst × Sst)} (hini : ∀ k, PureNF (ini k))
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (t n ΔFS ΔPCS : ℕ) :
    PureNF (smIdealView M ini Sch t n ΔFS ΔPCS) :=
  (pureNF_sample K).bind fun k => smSessView_pureNF hini Sch t n ΔFS ΔPCS _ k

/-! ## The adversary of the multi-challenge game -/

/-- The oracle tree of a distinguisher of the views: the schedule `Sch` on the public value `T`,
and the output bit of `D` on its view. -/
noncomputable def smHopPlay (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V)
    (D : V → SPComp Bool) (T : Pub) : OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) Bool :=
  (Sch T).bind fun v => .rand (outBool D v) .ret

/-- **The adversary of a distinguisher of the views** in the multi-challenge game: the challenge
epoch `t` and the tree `smHopPlay Sch D`. -/
noncomputable def smHopAdv (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V)
    (t : ℕ) (D : V → SPComp Bool) : SMSchemeAdv Pub Wd Ct Leak where
  tStar := PMF.pure t
  play _ T := smHopPlay Sch D T

/-- The multi-challenge game against `smHopAdv Sch t D` accepts with the probability that `D`
accepts the view of a session under a uniform key. -/
theorem smMultiGame_hopAdv [Fintype K] [Nonempty K] (M : SMScheme Sst Pub Rand Wd Ct Leak)
    (ini : K → SPComp (Pub × Sst × Sst)) (hM : M.init = SPComp.bind (SPComp.sample K) ini)
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (t n ΔFS ΔPCS : ℕ)
    (mode : ℕ → Bool) (D : V → SPComp Bool) (hD : ∀ v h, D v h = D v Heap.empty) :
    prTrue (smMultiGame M ΔFS ΔPCS n mode (smHopAdv Sch t D)) Heap.empty =
      prTrue (SPComp.bind (SPComp.bind (SPComp.sample K) (smSessView M ini Sch t n ΔFS ΔPCS mode))
        D) Heap.empty := by
  simp only [smMultiGame, smHopAdv, smHopPlay, ← liftPMF_pure, SPComp.pure_bind, hM,
    SPComp.bind_assoc, smSessView]
  refine prTrue_bind_congr _ (fun k h => prTrue_bind_congr _ (fun i h' => ?_) h) _
  rw [prTrue_liftPMF, prTrue_liftPMF_bind_of_const _ D hD, OracleAdv.run_bind]
  simp only [OracleAdv.run_rand, OracleAdv.run_ret, PMF.map_bind, PMF.pure_map, PMF.bind_pure,
    PMF.bind_map, Function.comp_def]

/-- **The advantage of a distinguisher of the views is a multi-challenge advantage.** For a
distinguisher `D` that does not read the heap, its advantage between the real game of a session
(a uniform key, then the real view) and the ideal view is the multi-challenge advantage of
`smHopAdv Sch t D`. -/
theorem advantageA_eq_multiAdvantage [Fintype K] [Nonempty K]
    (M : SMScheme Sst Pub Rand Wd Ct Leak) (ini : K → SPComp (Pub × Sst × Sst))
    (hM : M.init = SPComp.bind (SPComp.sample K) ini)
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (t n ΔFS ΔPCS : ℕ)
    (D : V → SPComp Bool) (hD : ∀ v h, D v h = D v Heap.empty) :
    AdvantageA (SPComp.bind (SPComp.sample K) (smRealView M ini Sch t n ΔFS ΔPCS))
        (smIdealView M ini Sch t n ΔFS ΔPCS) D =
      M.multiAdvantage ΔFS ΔPCS n (smHopAdv Sch t D) := by
  simp only [AdvantageA, SMScheme.multiAdvantage, Advantage, smIdealView,
    smMultiGame_hopAdv M ini hM Sch t n ΔFS ΔPCS _ D hD]
  rfl

end View

/-! ## The functionality and the ratchet layer -/

section Func

variable {K Sst Pub Rand Wd Ct Leak V : Type} [Fintype Rand] [Nonempty Rand] [Fintype K]
  [Nonempty K] [Inhabited K]

/-- **The ideal secure-messaging functionality `F_SM`** (Canetti–Jain–Swanberg–Varia), with the
forward-secrecy window `ΔFS` and the post-compromise window `ΔPCS`: the secure channel `F_SC`
whose session views are those of the schedule `Sch` over the scheme `M`. A session that
completed without exposure has the ideal view: under a fresh key, the challenge messages of the
honest epoch `t` have ideal ciphertexts, and a corruption leaks the state of the party only in
the windows that `ΔFS` and `ΔPCS` leave open around `t`. A session exposed by corruption of the
key exchange has the real view under the adversary key. -/
noncomputable def F_SM (M : SMScheme Sst Pub Rand Wd Ct Leak)
    (ini : K → SPComp (Pub × Sst × Sst))
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (t n ΔFS ΔPCS : ℕ) :
    Sys (St K) (HEv ⊕ AEv K) (HOut V ⊕ AOut) :=
  F_SC (smRealView M ini Sch t n ΔFS ΔPCS) (smIdealView M ini Sch t n ΔFS ΔPCS)

/-- **The ratchet layer** over a key exchange with adversary outputs `R`: at every key of a
`getKey` answer, the schedule `Sch` runs against the oracles of the corruption game over `M`
keyed by that key, with real ciphertexts; every other output passes. -/
noncomputable def smCorruptLayer {R : Type} (M : SMScheme Sst Pub Rand Wd Ct Leak)
    (ini : K → SPComp (Pub × Sst × Sst))
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (t n ΔFS ΔPCS : ℕ) :
    Sys Unit (HOut K ⊕ R) (HOut V ⊕ R) :=
  keyLayer (smRealView M ini Sch t n ΔFS ΔPCS)

/-- **The reduction to the corruption game** at the key `i` and the challenge `j`: the `j`-th
hybrid of the multi-challenge adversary of the reduction `hopRed i Z` of `SignalStackUC`. -/
noncomputable def smHopRed (M : SMScheme Sst Pub Rand Wd Ct Leak)
    (ini : K → SPComp (Pub × Sst × Sst))
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (t n ΔFS ΔPCS : ℕ)
    (i j : ℕ) {ζ : Type} (Z : Env (Strat ζ (HEv ⊕ AEv K) (HOut V ⊕ AOut)) ζ) :
    SMSchemeAdv Pub Wd Ct Leak :=
  (smHopAdv Sch t (hopRed (smRealView M ini Sch t n ΔFS ΔPCS)
    (smIdealView M ini Sch t n ΔFS ΔPCS) i Z)).hyb M n j

/-- The secure-messaging term of the key `i` is at most the sum over the `n` challenges of the
corruption advantages of `smHopRed i j Z`. -/
theorem advantageA_hopRed_le (M : SMScheme Sst Pub Rand Wd Ct Leak)
    (ini : K → SPComp (Pub × Sst × Sst)) (hM : M.init = SPComp.bind (SPComp.sample K) ini)
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (t n ΔFS ΔPCS i : ℕ)
    {ζ : Type} (Z : Env (Strat ζ (HEv ⊕ AEv K) (HOut V ⊕ AOut)) ζ) :
    AdvantageA (SPComp.bind (SPComp.sample K) (smRealView M ini Sch t n ΔFS ΔPCS))
        (smIdealView M ini Sch t n ΔFS ΔPCS)
        (hopRed (smRealView M ini Sch t n ΔFS ΔPCS) (smIdealView M ini Sch t n ΔFS ΔPCS) i Z) ≤
      ∑ j ∈ Finset.range n,
        M.corruptAdvantage ΔFS ΔPCS (smHopRed M ini Sch t n ΔFS ΔPCS i j Z) := by
  rw [advantageA_eq_multiAdvantage M ini hM Sch t n ΔFS ΔPCS _ (fun _ _ => rfl)]
  exact M.multiAdvantage_le ΔFS ΔPCS n _

end Func

/-! ## The Signal stack -/

section Stack

variable {S W K : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K]
  [Inhabited K] (G : DHGroup S W)
  {Sst Pub Rand Wd Ct Leak V : Type} [Fintype Rand] [Nonempty Rand]

/-- **The bound of the Signal stack with secure messaging** at an environment `Z`: the gap
Diffie–Hellman bound of X3DH at the environment reduced through the ratchet layer, and, at the
environment `Z'` reduced through the simulator, over the keys `i` below the number of
activations of `Z'`, the corruption advantages of the reductions `smHopRed i j Z'` over the `n`
challenges `j` and the probability that the key `i` is read twice. -/
noncomputable def fsmBound (P : Finset PartyId) (M : SMScheme Sst Pub Rand Wd Ct Leak)
    (ini : K → SPComp (Pub × Sst × Sst)) (hini : ∀ k, PureNF (ini k))
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (t n ΔFS ΔPCS : ℕ)
    (ζ : Type) (Z : Env (Strat ζ (OEv W) (HOut V ⊕ ROut S W K)) ζ) : ℝ≥0∞ :=
  gdhBound G P ((OProt.oracle (Q := OEv W) (A := OOut S W K)).reduction
      ((Hybrid.seqCtxR (E := OEv W) (smCorruptLayer M ini Sch t n ΔFS ΔPCS)
        (keyLayer_noFail fun k => (smSessView_pureNF hini Sch t n ΔFS ΔPCS _ k).2)).reduceEnv
          Z)) +
    ∑ i ∈ Finset.range ((simSC (V := V) G).reduceEnv (.inr .idle) Z).input.rounds,
      ((∑ j ∈ Finset.range n, M.corruptAdvantage ΔFS ΔPCS
          (smHopRed M ini Sch t n ΔFS ΔPCS i j ((simSC G).reduceEnv (.inr .idle) Z))) +
        prBad (hyb (smRealView M ini Sch t n ΔFS ΔPCS) (smIdealView M ini Sch t n ΔFS ΔPCS) i)
          (reuse i) ((simSC G).reduceEnv (.inr .idle) Z))

/-- **The Signal stack realizes secure messaging with corruption** (genuine UC).

*Ideal functionality.* `F_SM M ini Sch t n ΔFS ΔPCS`: the multi-session secure channel of
`F_AKE` with unlinked delivery whose completed sessions have the ideal view of the schedule
`Sch` (ideal ciphertexts for the challenge messages of the honest epoch `t`, the states leaked
in the corruption windows of `ΔFS` and `ΔPCS` under a fresh key), whose exposed sessions have
the real view under the adversary key, and whose adversary port is that of `F_AKE`.

*Real world.* The real X3DH protocol `x3dhReal G` followed by the ratchet layer
`smCorruptLayer M ini Sch t n ΔFS ΔPCS`, which runs the schedule against the oracles of the
scheme `M` keyed by the session key of every `getKey` answer.

*Simulator.* `scSim G`, the X3DH simulator over `F_SC`: it keeps a copy of the real state, draws
the long-term and session secrets, forwards the honest events, and passes the key-derivation
value to `newKey` for an exposed session and the default key otherwise.

*Bound.* For a scheme whose initialisation is the keyed initialisation `ini` at a uniform key,
with `ini k` neither touching the heap nor failing, for every finite set of parties `P` and every
environment `Z`, the distance is at most `fsmBound`: the gap Diffie–Hellman bound of X3DH, and a
sum over the keys of the run of the corruption advantages of the explicit reductions
`smHopRed i j` over the challenges `j < n` and of the probability that a key is read twice. -/
theorem signal_stack_realizes_FSM (P : Finset PartyId) (M : SMScheme Sst Pub Rand Wd Ct Leak)
    (ini : K → SPComp (Pub × Sst × Sst)) (hM : M.init = SPComp.bind (SPComp.sample K) ini)
    (hini : ∀ k, PureNF (ini k))
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (t n ΔFS ΔPCS : ℕ) :
    RealizesSim ((x3dhReal (K := K) G).seq (smCorruptLayer M ini Sch t n ΔFS ΔPCS))
      (F_SM M ini Sch t n ΔFS ΔPCS) (scSim G) (fsmBound G P M ini hini Sch t n ΔFS ΔPCS) := by
  have hR : ∀ k, SPComp.IsPure (smRealView M ini Sch t n ΔFS ΔPCS k) ∧
      SPComp.NoFail (smRealView M ini Sch t n ΔFS ΔPCS k) := fun k =>
    smSessView_pureNF hini Sch t n ΔFS ΔPCS _ k
  have h := stack_realizes_FSC_of (x3dhReal (K := K) G) (simProt G) (simProt_opaque G) x3dhFwd
    (simProt_isFwd G) (x3dh_realizesSim_gapDH G P) (smRealView M ini Sch t n ΔFS ΔPCS)
    (smIdealView M ini Sch t n ΔFS ΔPCS) hR (smIdealView_pureNF hini Sch t n ΔFS ΔPCS)
  intro ζ Z
  refine (h ζ Z).trans ?_
  simp only [fsmBound, scBound]
  exact add_le_add le_rfl (Finset.sum_le_sum fun i _ =>
    add_le_add_left (advantageA_hopRed_le M ini hM Sch t n ΔFS ΔPCS i _) _)

/-- **The Signal stack over a scheme that simulates another one** (genuine UC). For a scheme
`M'` that simulates `M` (`SMScheme.Sim`), whose initialisation is the keyed initialisation
`ini'` at a uniform key, the stack over `M'` realizes `F_SM M' ini' Sch t n ΔFS ΔPCS` behind
`scSim G` with the bound of `signal_stack_realizes_FSM` in which each corruption advantage over
`M'` is the corruption advantage over `M` of the reduction with the answers encoded
(`SMSchemeAdv.comap`). The ideal functionality, the real world and the simulator are those of
`signal_stack_realizes_FSM` at `M'`. -/
theorem signal_stack_realizes_FSM_sim {Sst' Pub' Ct' Leak' : Type} (P : Finset PartyId)
    {M' : SMScheme Sst' Pub' Rand Wd Ct' Leak'} {M : SMScheme Sst Pub Rand Wd Ct Leak}
    {ρ : Sst' → Sst → Prop} {encP : Pub → Pub'} {encC : Ct → Ct'} {encL : Leak → Leak'}
    {encI : Sst → Sst'} (hS : M'.Sim M ρ encP encC encL encI)
    (ini' : K → SPComp (Pub' × Sst' × Sst')) (hM : M'.init = SPComp.bind (SPComp.sample K) ini')
    (hini : ∀ k, PureNF (ini' k))
    (Sch : Pub' → OracleAdv (SMQuery Wd) (SMSchemeAns Pub' Ct' Leak') V) (t n ΔFS ΔPCS : ℕ) :
    RealizesSim ((x3dhReal (K := K) G).seq (smCorruptLayer M' ini' Sch t n ΔFS ΔPCS))
      (F_SM M' ini' Sch t n ΔFS ΔPCS) (scSim G) (fun _ Z =>
        gdhBound G P ((OProt.oracle (Q := OEv W) (A := OOut S W K)).reduction
          ((Hybrid.seqCtxR (E := OEv W) (smCorruptLayer M' ini' Sch t n ΔFS ΔPCS)
            (keyLayer_noFail fun k => (smSessView_pureNF hini Sch t n ΔFS ΔPCS _ k).2)).reduceEnv
              Z)) +
        ∑ i ∈ Finset.range ((simSC (V := V) G).reduceEnv (.inr .idle) Z).input.rounds,
          ((∑ j ∈ Finset.range n, M.corruptAdvantage ΔFS ΔPCS
              ((smHopRed M' ini' Sch t n ΔFS ΔPCS i j
                ((simSC G).reduceEnv (.inr .idle) Z)).comap encP encC encL)) +
            prBad (hyb (smRealView M' ini' Sch t n ΔFS ΔPCS)
              (smIdealView M' ini' Sch t n ΔFS ΔPCS) i)
              (reuse i) ((simSC G).reduceEnv (.inr .idle) Z))) := by
  intro ζ Z
  refine (signal_stack_realizes_FSM G P M' ini' hM hini Sch t n ΔFS ΔPCS ζ Z).trans (le_of_eq ?_)
  simp only [fsmBound, hS.corruptAdvantage_eq]

end Stack

/-! ## The ACD construction -/

section ACD

variable {S W : Type} [Field S] [Fintype S] [SampleableType W] (G : DHGroup S W)
  {Sc Msg Key Rand RK Sa Wd Ct V : Type} [Fintype Rand] [Nonempty Rand] [SampleableType Wd]
  [SampleableType Ct]

open CatCrypt.Crypto.Assumptions CatCrypt.Crypto.PRPPRF

/-- **The keyed initialisation of the ACD construction**: the CKA initialisation, and both
parties with the root key `rk` and no chains. -/
noncomputable def acdIni (C : CKADef Sc Msg Key) (rk : RK) :
    SPComp (Msg × SMPartySt Sc RK Sa × SMPartySt Sc RK Sa) :=
  SPComp.bind C.init fun i =>
    SPComp.pure (i.1, (⟨i.2.1, rk, none, none⟩ : SMPartySt Sc RK Sa), ⟨i.2.2, rk, none, none⟩)

/-- The keyed initialisation of a CKA whose initialisation neither touches the heap nor fails
neither touches the heap nor fails. -/
theorem acdIni_pureNF {C : CKADef Sc Msg Key} (hC : PureNF C.init) (rk : RK) :
    PureNF (acdIni (Sa := Sa) C rk) :=
  hC.bind fun _ => CatCrypt.Crypto.PAKE.CPaceSquare.pureNF_pure _

variable [Fintype RK] [Nonempty RK]

omit [Fintype Rand] [Nonempty Rand] in
/-- The initialisation of `acdSM` is its keyed initialisation at a uniform root key, for a CKA
initialisation that does not touch the heap. -/
theorem acdSM_init_eq (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (Gc : PRGDef Sa (Wd × Sa)) (D : AEADDef Wd Ct)
    (hC : SPComp.IsPure C.init) :
    (acdSM C R Gc D).init = SPComp.bind (SPComp.sample RK) (acdIni (Sa := Sa) C) := by
  simp only [acdSM]
  exact SPComp.isPure_bind_comm_left _ _ _ hC

variable [Inhabited RK]

/-- **The Signal stack over the double ratchet of ACD realizes secure messaging with
corruption** (genuine UC): `signal_stack_realizes_FSM` at `acdSM C R Gc D` keyed through
`acdIni C`, for a CKA that neither touches the heap nor fails. The ideal functionality is
`F_SM (acdSM C R Gc D) (acdIni C) Sch t n ΔFS ΔPCS`, the real world is X3DH followed by the
ratchet layer over `acdSM C R Gc D` with the session key as the first root key, the simulator
is `scSim G`, and the bound is `fsmBound` over `acdSM C R Gc D`. -/
theorem signal_stack_realizes_FSM_acd (P : Finset PartyId) (C : CKADef Sc Msg Key)
    [CKACoins C Rand] (hC : CKAPureNF C) (R : PRGDef (RK × Key) (RK × Sa))
    (Gc : PRGDef Sa (Wd × Sa)) (D : AEADDef Wd Ct)
    (Sch : Msg → OracleAdv (SMQuery Wd) (SMSchemeAns Msg Ct (SMPartySt Sc RK Sa)) V)
    (t n ΔFS ΔPCS : ℕ) :
    RealizesSim ((x3dhReal (K := RK) G).seq
        (smCorruptLayer (acdSM C R Gc D) (acdIni C) Sch t n ΔFS ΔPCS))
      (F_SM (acdSM C R Gc D) (acdIni C) Sch t n ΔFS ΔPCS) (scSim G)
      (fsmBound G P (acdSM C R Gc D) (acdIni C) (acdIni_pureNF hC.1) Sch t n ΔFS ΔPCS) :=
  signal_stack_realizes_FSM G P (acdSM C R Gc D) (acdIni C)
    (acdSM_init_eq C R Gc D hC.1.1) (acdIni_pureNF hC.1) Sch t n ΔFS ΔPCS

end ACD

/-! ## Running time of the reductions -/

section Timed

variable {Sst Pub Rand Wd Ct Leak V : Type}

open OracleAdv.Timed

derive_timed smHopPlay

/-- **Time of the tree of a distinguisher of the views.** For a costed schedule whose tree at
`T` takes time at most `tS` and a distinguisher whose output bit costs at most `tD` on every
view, the costed form of `smHopPlay Sch D T` takes time at most `1 + SchCost T + tS + tD + 7`. -/
theorem smHopPlay.timeBound_timed
    (Sch : Pub → OracleAdv.Timed (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (SchCost : Pub → ℕ)
    (D : V → SPComp Bool) (DCost : V → ℕ) (T : Pub) {tS tD : ℕ} (hS : (Sch T).TimeBound tS)
    (hD : ∀ v, DCost v ≤ tD) :
    StepTimeBound (smHopPlay.timed Sch SchCost D DCost T) (1 + SchCost T + (tS + (tD + 7))) := by
  unfold smHopPlay.timed
  refine stepTimeBound_delay (timeBound_bind hS fun v => ?_)
  have hv := hD v
  exact ⟨by omega, by omega, fun _ => ⟨by grind, trivial⟩⟩

/-- **Time of the reduction `smHopRed`.** For a costed schedule `Sch` whose tree at `T₀` takes
time at most `tS` and asks at most `q` queries, and a distinguisher `D` whose output bit costs at
most `tD` on every view, the costed `j`-th hybrid of the costed tree of `smHopPlay Sch D` at the
step cost `u` of the handler erases to the play of the `j`-th hybrid of `smHopAdv Sch t D` and
takes time at most `1 + SchCost T₀ + tS + tD + 7 + q * (u + 2)`. For `D = hopRed i Z`, the cost
`DCost v` of its output bit is the time of the costed tree of `hopRed i Z` at `v`, which
`hopRed.timeBound_timed` of `SignalStackUC` bounds uniformly in `v`. -/
theorem smHopRed.timeBound_timed (M : SMScheme Sst Pub Rand Wd Ct Leak)
    (Sch : Pub → OracleAdv.Timed (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (SchCost : Pub → ℕ)
    (D : V → SPComp Bool) (DCost : V → ℕ) (t n j u : ℕ) (T₀ : Pub) {tS tD q : ℕ}
    (hS : (Sch T₀).TimeBound tS) (hD : ∀ v, DCost v ≤ tD) (hq : (Sch T₀).erase.IsQueryBound q) :
    (delay (smHopPlay.timed Sch SchCost D DCost T₀).1
        (SMSchemeAdv.hybPlayTimed M t n j u (smHopPlay.timed Sch SchCost D DCost T₀).2)).2.erase =
        ((smHopAdv (fun a => (Sch a).erase) t D).hyb M n j).play t T₀ ∧
      StepTimeBound (delay (smHopPlay.timed Sch SchCost D DCost T₀).1
        (SMSchemeAdv.hybPlayTimed M t n j u (smHopPlay.timed Sch SchCost D DCost T₀).2))
        (1 + SchCost T₀ + (tS + (tD + 7)) + q * (u + 2)) := by
  have h1 := smHopPlay.timeBound_timed Sch SchCost D DCost T₀ hS hD
  have he : (smHopPlay.timed Sch SchCost D DCost T₀).2.erase =
      (smHopAdv (fun a => (Sch a).erase) t D).play t T₀ := smHopPlay.erase_timed _ _ _ _ _
  have hq' : (smHopPlay.timed Sch SchCost D DCost T₀).2.erase.IsQueryBound q := by
    rw [he]
    exact OracleAdv.isQueryBound_bind (n := 0)
      (f := fun v => OracleAdv.rand (outBool D v) OracleAdv.ret) hq fun _ _ => trivial
  obtain ⟨h2, h3⟩ := SMSchemeAdv.hybPlayTimed_time M n j u (smHopAdv _ t D) t T₀ _ he h1.2 hq'
  refine ⟨h2, (stepTimeBound_delay h3).mono ?_⟩
  have := h1.1
  omega

end Timed

end CatCrypt.Crypto.Messaging.SignalStackSM
