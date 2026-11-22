/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SignalStackSM
public import CatCryptCore.Crypto.Messaging.SMPrekey
public import CatCryptCore.Crypto.Messaging.SMCorruptPrekey
public import CatCryptCore.Crypto.AKE.X3DHSquarePrekey

/-!
# The Signal stack with the signed prekey realizes secure messaging with corruption

The Signal stack runs X3DH and keys the ratchet with the session key and the signed-prekey secret
of the responder of the session, a datum that both partners share. This module proves that the
stack realizes the secure-messaging functionality `F_SMK` with that datum behind the X3DH
simulator with the datum, in the sense of Canetti, Jain, Swanberg and Varia (CRYPTO 2022).

**The session.** A family of schemes `M : S → SMScheme Sst Pub Rand Wd Ct Leak` indexed by the
datum, each keyed by the session key through the keyed initialisation `ini · x₀` with
`(M x₀).init = SPComp.bind (SPComp.sample K) (ini · x₀)`. The real view of a session with the key
`k` and the datum `x₀` is `smRealViewK M ini Sch t n ΔFS ΔPCS (k, x₀)`, the real view of
`SignalStackSM` over `M x₀`; its ideal view at the datum `x₀` is `smIdealViewK`.

**The ideal functionality.** `F_SMK M ini Sch t n ΔFS ΔPCS` is the functionality with a datum
`F_SCK` of `SignalStackUC` at the split `prekeySplit K S` of a key `(k, x₀)` into the secret part
`k` and the datum `x₀`: a session that completed without exposure has the ideal view at its
datum, an exposed session the real view under the adversary key and datum.

**The real world.** `(x3dhRealPair G).seq (smCorruptLayerK M ini Sch t n ΔFS ΔPCS)`: X3DH whose
`getKey` answers carry the prekey secret of the responder, and the ratchet layer keyed by the
pair.

**The simulator.** `chanSim (simProtPair G) x3dhFwd`: the X3DH simulator with the datum of
`X3DHSquarePrekey`, its decisions read over `F_SMK`.

**The bound.** `fsmBoundPair`: the gap Diffie–Hellman bound of the X3DH square with the datum at
the environment reduced through an efficient layer `Leff` that reads the datum only through its
public value, and, per key of the run, the chosen-datum advantage of the two-stage reduction
`hopRedK` of `SignalStackUC`. That advantage is at most the expectation over the first stage of
the corruption advantages over `M x₀` of the hybrid adversaries `(smHopAdv Sch t D).hyb (M x₀) n j`
at the datum `x₀` chosen by the first stage (`CDAdv.advantage_le_tsum`). For the gated double
ratchet of ACD at the signed-prekey pair, the layer of `smPreView` is the efficient one
(`smSessView_pair_eq_pre`) and each corruption advantage has the bound of
`sm_dh_corrupt_advantage_le_pair` (`signal_stack_realizes_FSM_acd_prekey`). The term of a key
also contains the probability that the key is read twice, which is `1` when both partners of an
unexposed session always read their key; the bound is then at least `1`. Each `getKey` runs a
session of its own, and the partners share no channel.

## Main definitions

* `cdGuessAt`: the second stage of a two-stage adversary at a state and a heap.
* `prekeySplit`, `smRealViewK`, `smIdealViewK`, `F_SMK`, `smCorruptLayerK`: the split, the
  views, the functionality and the ratchet layer with the datum.
* `smKeyTermK`, `fsmBoundPair`: the term of a key and the bound of the stack.
* `smPreView`, `smPairBound`: the efficient layer and the bound of the gated ACD ratchet at the
  signed-prekey pair.

## Main results

* `CDAdv.advantage_le_tsum`: the chosen-datum advantage is at most the expectation of the
  advantages at the chosen data.
* `signal_stack_realizes_FSM_prekey`: the stack with the datum realizes `F_SMK`.
* `signal_stack_realizes_FSM_acd_prekey`: the same for the gated ACD ratchet at the signed-prekey
  pair, with the bound of `sm_dh_corrupt_advantage_le_pair`.

## References

* R. Canetti, P. Jain, M. Swanberg, M. Varia, *Universally composable end-to-end secure
  messaging*, CRYPTO 2022.
* J. Alwen, S. Coretti, Y. Dodis, *The double ratchet: security notions, proofs, and
  modularization for the Signal protocol*, Eurocrypt 2019.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Messaging.SignalStackSMPrekey

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Messaging
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.AKE.X3DHSquare CatCrypt.Crypto.AKE.X3DHSquareGDH
open CatCrypt.Crypto.AKE.X3DHSquarePrekey
open CatCrypt.Crypto.Messaging.SignalStack CatCrypt.Crypto.Messaging.SignalStackUC
open CatCrypt.Crypto.Messaging.SignalStackSM
open CatCrypt.Crypto.PAKE.CPaceSquare (PureNF pureNF_sample pureNF_pure)
open CatCrypt.Crypto.PAKE.DHExtract
open scoped ENNReal

/-! ## Two-stage adversaries at a fixed state -/

section CD

/-- After a computation that does not touch the heap, the acceptance probability of `k` from the
heap `h₀` is the acceptance probability from the empty heap of the continuation that runs `k`
from `h₀`. -/
theorem prTrue_bind_isPure_heap {α : Type} {c : SPComp α} (hc : SPComp.IsPure c)
    (k : α → SPComp Bool) (h₀ : Heap) :
    prTrue (SPComp.bind c k) h₀ =
      prTrue (SPComp.bind c fun a => (fun _ => k a h₀ : SPComp Bool)) Heap.empty := by
  obtain ⟨μ, hμ⟩ := hc
  have e : ∀ (k' : α → SPComp Bool) (h : Heap),
      SPComp.bind c k' h = μ.bind fun a => k' a h := by
    intro k' h
    rw [SPComp.bind_def, hμ, SDistr.bind_assoc]
    simp only [SDistr.pure_bind]
  unfold prTrue
  grind

/-- The advantage between two continuations of one computation is at most the expectation over
the outcomes `(a, h)` of the computation of the gap between the acceptance probabilities of the
continuations at `a` from `h`. -/
theorem advantage_bind_le_tsum {α : Type} (c : SPComp α) (f g : α → SPComp Bool) :
    Advantage (SPComp.bind c f) (SPComp.bind c g) ≤
      ∑' p : Option (α × Heap), (c Heap.empty : PMF _) p *
        p.elim 0 fun q => (prTrue (f q.1) q.2 - prTrue (g q.1) q.2) ⊔
          (prTrue (g q.1) q.2 - prTrue (f q.1) q.2) := by
  have hw : ∀ k : α → SPComp Bool, prTrue (SPComp.bind c k) Heap.empty =
      ∑' p : Option (α × Heap), (c Heap.empty : PMF _) p *
        p.elim 0 fun q => prTrue (k q.1) q.2 := by
    intro k
    rw [ForkingLemma.prTrue_bind_eq_weighted]
    refine tsum_congr fun p => ?_
    rcases p with _ | ⟨a, h⟩ <;> rfl
  have key : ∀ a b : Option (α × Heap) → ℝ≥0∞,
      ∑' p, (c Heap.empty : PMF _) p * a p - ∑' p, (c Heap.empty : PMF _) p * b p ≤
        ∑' p, (c Heap.empty : PMF _) p * ((a p - b p) ⊔ (b p - a p)) := by
    intro a b
    rw [tsub_le_iff_left, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun i => ?_
    rw [← mul_add]
    gcongr
    calc a i ≤ (a i - b i) + b i := le_tsub_add
      _ ≤ _ := by rw [add_comm]; gcongr; exact le_sup_left
  simp only [Advantage, hw]
  refine max_le ((key _ _).trans (le_of_eq (tsum_congr fun p => ?_)))
    ((key _ _).trans (le_of_eq (tsum_congr fun p => ?_)))
  · rcases p with _ | q <;> simp
  · rcases p with _ | q <;> simp [max_comm]

variable {σ D V : Type}

/-- **The second stage of a two-stage adversary at a state and a heap**: the guess of `A` from
the state `s` on the view `v`, run from the heap `h` whatever the heap it is started from. -/
noncomputable def cdGuessAt (A : CDAdv σ D V) (s : σ) (h : Heap) (v : V) : SPComp Bool :=
  fun _ => A.guess s v h

/-- **The chosen-datum advantage is at most the expectation of the advantages at the chosen
data.** For views that do not touch the heap, the chosen-datum advantage of `A` is at most the
expectation over the outcomes `((s, d), h)` of the first stage of the advantage of the
distinguisher `cdGuessAt A s h` between `real d` and `ideal d`. -/
theorem CDAdv.advantage_le_tsum (A : CDAdv σ D V) (real ideal : D → SPComp V)
    (hr : ∀ d, SPComp.IsPure (real d)) (hi : ∀ d, SPComp.IsPure (ideal d)) :
    A.advantage real ideal ≤
      ∑' p : Option ((σ × D) × Heap), (A.pre Heap.empty : PMF _) p *
        p.elim 0 fun q => AdvantageA (real q.1.2) (ideal q.1.2) (cdGuessAt A q.1.1 q.2) := by
  unfold CDAdv.advantage CDAdv.game
  refine (advantage_bind_le_tsum A.pre _ _).trans (le_of_eq (tsum_congr fun p => ?_))
  rcases p with _ | ⟨⟨s, d⟩, h⟩
  · rfl
  · simp only [Option.elim, AdvantageA, Advantage]
    rw [prTrue_bind_isPure_heap (hr d), prTrue_bind_isPure_heap (hi d)]
    rfl

end CD

/-! ## The functionality and the ratchet layer with the datum -/

section Func

variable {K S Sst Pub Rand Wd Ct Leak V : Type} [Fintype Rand] [Nonempty Rand] [Fintype K]
  [Nonempty K] [Inhabited K] [Fintype S] [Inhabited S]

/-- **The split of a key with the prekey datum**: the key `(k, x₀)` has the secret part `k` and
the datum `x₀`. -/
def prekeySplit (K S : Type) : KeySplit (K × S) K S where
  key := Prod.mk
  dat := Prod.snd
  dat_key _ _ := rfl

/-- **The real view of a session with the datum**: the real view over the scheme `M x₀` of the
datum `x₀`, keyed by `k` through the keyed initialisation `ini · x₀`. -/
noncomputable def smRealViewK (M : S → SMScheme Sst Pub Rand Wd Ct Leak)
    (ini : K → S → SPComp (Pub × Sst × Sst))
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (t n ΔFS ΔPCS : ℕ)
    (p : K × S) : SPComp V :=
  smRealView (M p.2) (fun k => ini k p.2) Sch t n ΔFS ΔPCS p.1

/-- **The ideal view of a session at the datum `x₀`**: the ideal view over `M x₀`. -/
noncomputable def smIdealViewK (M : S → SMScheme Sst Pub Rand Wd Ct Leak)
    (ini : K → S → SPComp (Pub × Sst × Sst))
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (t n ΔFS ΔPCS : ℕ)
    (x₀ : S) : SPComp V :=
  smIdealView (M x₀) (fun k => ini k x₀) Sch t n ΔFS ΔPCS

/-- **The ideal secure-messaging functionality with the prekey datum `F_SMK`**: the secure
channel with a datum `F_SCK` at the split `prekeySplit K S`, whose completed sessions have the
ideal view `smIdealViewK` at their datum and whose exposed sessions have the real view
`smRealViewK` under the adversary key and datum. -/
noncomputable def F_SMK (M : S → SMScheme Sst Pub Rand Wd Ct Leak)
    (ini : K → S → SPComp (Pub × Sst × Sst))
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (t n ΔFS ΔPCS : ℕ) :
    Sys (St (K × S)) (HEv ⊕ AEv (K × S)) (HOut V ⊕ AOut) :=
  F_SCK (prekeySplit K S) (smRealViewK M ini Sch t n ΔFS ΔPCS)
    (smIdealViewK M ini Sch t n ΔFS ΔPCS)

/-- **The ratchet layer with the datum**: at the key and datum of every `getKey` answer, the
real view `smRealViewK`; every other output passes. -/
noncomputable def smCorruptLayerK {R : Type} (M : S → SMScheme Sst Pub Rand Wd Ct Leak)
    (ini : K → S → SPComp (Pub × Sst × Sst))
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (t n ΔFS ΔPCS : ℕ) :
    Sys Unit (HOut (K × S) ⊕ R) (HOut V ⊕ R) :=
  keyLayer (smRealViewK M ini Sch t n ΔFS ΔPCS)

/-- **The term of the key `i`** at an environment `Z` of the functionality, for a bound `β` of the
corruption advantages over `M x₀` at the datum `x₀`: the expectation over the outcomes
`((s, x₀), h)` of the first stage of the reduction `hopRedK i Z` of the sum over the `n`
challenges `j` of `β x₀` at the `j`-th hybrid of the multi-challenge adversary of its second stage
at `s` and `h`, plus the probability that the key `i` is read twice. -/
noncomputable def smKeyTermK (M : S → SMScheme Sst Pub Rand Wd Ct Leak)
    (ini : K → S → SPComp (Pub × Sst × Sst)) (β : S → SMSchemeAdv Pub Wd Ct Leak → ℝ≥0∞)
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (t n ΔFS ΔPCS i : ℕ)
    {ζ : Type} (Z : Env (Strat ζ (HEv ⊕ AEv (K × S)) (HOut V ⊕ AOut)) ζ) : ℝ≥0∞ :=
  (∑' p, ((hopRedK (prekeySplit K S) (smRealViewK M ini Sch t n ΔFS ΔPCS)
      (smIdealViewK M ini Sch t n ΔFS ΔPCS) i Z).pre Heap.empty : PMF _) p *
    p.elim 0 fun q => ∑ j ∈ Finset.range n, β q.1.2
      ((smHopAdv Sch t (cdGuessAt (hopRedK (prekeySplit K S) (smRealViewK M ini Sch t n ΔFS ΔPCS)
        (smIdealViewK M ini Sch t n ΔFS ΔPCS) i Z) q.1.1 q.2)).hyb (M q.1.2) n j)) +
  prBad (hybK (prekeySplit K S) (smRealViewK M ini Sch t n ΔFS ΔPCS)
    (smIdealViewK M ini Sch t n ΔFS ΔPCS) i) (reuse i) Z

omit [Fintype S] in
/-- The term of a key is monotone in the bound of the corruption advantages. -/
theorem smKeyTermK_mono (M : S → SMScheme Sst Pub Rand Wd Ct Leak)
    (ini : K → S → SPComp (Pub × Sst × Sst)) {β β' : S → SMSchemeAdv Pub Wd Ct Leak → ℝ≥0∞}
    (hβ : ∀ d A, β d A ≤ β' d A)
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (t n ΔFS ΔPCS i : ℕ)
    {ζ : Type} (Z : Env (Strat ζ (HEv ⊕ AEv (K × S)) (HOut V ⊕ AOut)) ζ) :
    smKeyTermK M ini β Sch t n ΔFS ΔPCS i Z ≤ smKeyTermK M ini β' Sch t n ΔFS ΔPCS i Z := by
  unfold smKeyTermK
  refine add_le_add (ENNReal.tsum_le_tsum fun p => mul_le_mul' le_rfl ?_) le_rfl
  rcases p with _ | q
  · exact le_rfl
  · exact Finset.sum_le_sum fun j _ => hβ _ _

omit [Fintype S] in
/-- **The bound of the hybrid argument with the datum by corruption advantages.** For schemes
whose initialisations are the keyed initialisations at a uniform key, with `ini k x₀` neither
touching the heap nor failing, `scBoundK` at the split `prekeySplit K S` is at most the sum over
the keys of the run of `smKeyTermK` with the corruption advantages over `M x₀`. -/
theorem scBoundK_le_keyTermK (M : S → SMScheme Sst Pub Rand Wd Ct Leak)
    (ini : K → S → SPComp (Pub × Sst × Sst))
    (hM : ∀ x₀, (M x₀).init = SPComp.bind (SPComp.sample K) fun k => ini k x₀)
    (hini : ∀ k x₀, PureNF (ini k x₀))
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (t n ΔFS ΔPCS : ℕ)
    {ζ : Type} (Z : Env (Strat ζ (HEv ⊕ AEv (K × S)) (HOut V ⊕ AOut)) ζ) :
    scBoundK (prekeySplit K S) (smRealViewK M ini Sch t n ΔFS ΔPCS)
        (smIdealViewK M ini Sch t n ΔFS ΔPCS) Z ≤
      ∑ i ∈ Finset.range Z.input.rounds,
        smKeyTermK M ini (fun d => (M d).corruptAdvantage ΔFS ΔPCS) Sch t n ΔFS ΔPCS i Z := by
  rw [scBoundK, scBoundImp]
  refine Finset.sum_le_sum fun i _ => add_le_add ?_ le_rfl
  refine (CDAdv.advantage_le_tsum _ _ _ (fun d => ?_) (fun d => ?_)).trans
    (ENNReal.tsum_le_tsum fun p => mul_le_mul' le_rfl ?_)
  · exact ((pureNF_sample K).bind fun k =>
      smSessView_pureNF (fun k => hini k d) Sch t n ΔFS ΔPCS _ k).1
  · exact (smIdealView_pureNF (fun k => hini k d) Sch t n ΔFS ΔPCS).1
  · rcases p with _ | ⟨⟨s, d⟩, h⟩
    · exact le_rfl
    · exact (le_of_eq (advantageA_eq_multiAdvantage (M d) (fun k => ini k d) (hM d) Sch t n
        ΔFS ΔPCS _ fun _ _ => rfl)).trans ((M d).multiAdvantage_le ΔFS ΔPCS n _)

end Func

/-! ## The Signal stack with the datum -/

section Stack

variable {S W K : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K]
  [Inhabited K] (G : DHGroup S W)
  {Sst Pub Rand Wd Ct Leak V : Type} [Fintype Rand] [Nonempty Rand]

/-- **The bound of the Signal stack with the prekey datum** at an environment `Z`, for a bound
`β` of the corruption advantages at a datum and an efficient layer `Leff` that never fails: the
gap Diffie–Hellman bound of the X3DH square with the datum at the environment reduced through
`Leff`, and, at the environment `Z'` reduced through the simulator, over the keys `i` below the
number of activations of `Z'`, the term `smKeyTermK` of the key `i`. -/
noncomputable def fsmBoundPair [Inhabited S] (P : Finset PartyId)
    (M : S → SMScheme Sst Pub Rand Wd Ct Leak) (ini : K → S → SPComp (Pub × Sst × Sst))
    (β : S → SMSchemeAdv Pub Wd Ct Leak → ℝ≥0∞)
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (t n ΔFS ΔPCS : ℕ)
    (Leff : K × W → SPComp V) (hLeff : ∀ k, SPComp.NoFail (Leff k))
    (ζ : Type) (Z : Env (Strat ζ (OEv W) (HOut V ⊕ ROut S W K)) ζ) : ℝ≥0∞ :=
  gdhBound G P ((withPub (S := S) (K := K)).reduction
      ((Hybrid.seqCtxR (E := OEv W) (keyLayer (R := ROut S W K) Leff)
        (keyLayer_noFail hLeff)).reduceEnv Z)) +
    ∑ i ∈ Finset.range
        ((simSCOver (V := V) (simProtPair (K := K) G) x3dhFwd).reduceEnv (.inr .idle)
          Z).input.rounds,
      smKeyTermK M ini β Sch t n ΔFS ΔPCS i
        ((simSCOver (simProtPair (K := K) G) x3dhFwd).reduceEnv (.inr .idle) Z)

/-- The bound of the stack is monotone in the bound of the corruption advantages. -/
theorem fsmBoundPair_mono [Inhabited S] (P : Finset PartyId)
    (M : S → SMScheme Sst Pub Rand Wd Ct Leak) (ini : K → S → SPComp (Pub × Sst × Sst))
    {β β' : S → SMSchemeAdv Pub Wd Ct Leak → ℝ≥0∞} (hβ : ∀ d A, β d A ≤ β' d A)
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (t n ΔFS ΔPCS : ℕ)
    (Leff : K × W → SPComp V) (hLeff : ∀ k, SPComp.NoFail (Leff k))
    (ζ : Type) (Z : Env (Strat ζ (OEv W) (HOut V ⊕ ROut S W K)) ζ) :
    fsmBoundPair G P M ini β Sch t n ΔFS ΔPCS Leff hLeff ζ Z ≤
      fsmBoundPair G P M ini β' Sch t n ΔFS ΔPCS Leff hLeff ζ Z :=
  add_le_add le_rfl (Finset.sum_le_sum fun i _ => smKeyTermK_mono M ini hβ Sch t n ΔFS ΔPCS i _)

/-- **The Signal stack with the signed prekey realizes secure messaging with corruption**
(genuine UC).

*Ideal functionality.* `F_SMK M ini Sch t n ΔFS ΔPCS`: the multi-session functionality over
`F_AKEK` with unlinked delivery and the prekey datum, whose completed sessions have the ideal
view of the schedule `Sch` over `M x₀` at their datum `x₀`, whose exposed sessions have the real
view under the adversary key and datum, and whose adversary port is that of `F_AKEK`.

*Real world.* The real X3DH protocol with the datum `x3dhRealPair G` followed by the ratchet
layer `smCorruptLayerK M ini Sch t n ΔFS ΔPCS`, which runs the schedule against the oracles of
the scheme `M x₀` keyed by the session key `k` of every `getKey` answer `(k, x₀)`.

*Simulator.* `chanSim (simProtPair G) x3dhFwd`: the X3DH simulator with the datum; it keeps a
copy of the real state, draws the long-term and session secrets, forwards the honest events, and
proposes to `newKey` the key-derivation value with the prekey secret of the responder for an
exposed session and the default key with that secret otherwise.

*Bound.* For schemes whose initialisations are the keyed initialisations at a uniform key, with
`ini k x₀` neither touching the heap nor failing, and a layer `Leff` that never fails and gives
the real view at `(k, x₀)` from `(k, G.pub x₀)`, for every finite set of parties `P` and every
environment `Z`, the distance is at most `fsmBoundPair` with the corruption advantages over
`M x₀`: the gap Diffie–Hellman bound of X3DH at the environment reduced through `Leff`, and per
key the expectation over the chosen datum of the corruption advantages of the hybrid adversaries
`(smHopAdv Sch t D).hyb (M x₀) n j` and the probability that a key is read twice. -/
theorem signal_stack_realizes_FSM_prekey [Inhabited S] (P : Finset PartyId)
    (M : S → SMScheme Sst Pub Rand Wd Ct Leak) (ini : K → S → SPComp (Pub × Sst × Sst))
    (hM : ∀ x₀, (M x₀).init = SPComp.bind (SPComp.sample K) fun k => ini k x₀)
    (hini : ∀ k x₀, PureNF (ini k x₀))
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (t n ΔFS ΔPCS : ℕ)
    (Leff : K × W → SPComp V) (hLeff : ∀ k, SPComp.NoFail (Leff k))
    (hL : ∀ k x₀, smRealViewK M ini Sch t n ΔFS ΔPCS (k, x₀) = Leff (k, G.pub x₀)) :
    RealizesSim ((x3dhRealPair (K := K) G).seq (smCorruptLayerK M ini Sch t n ΔFS ΔPCS))
      (F_SMK M ini Sch t n ΔFS ΔPCS) (chanSim (simProtPair (K := K) G) x3dhFwd)
      (fsmBoundPair G P M ini (fun d => (M d).corruptAdvantage ΔFS ΔPCS) Sch t n ΔFS ΔPCS Leff
        hLeff) := by
  have hR : ∀ p, SPComp.IsPure (smRealViewK M ini Sch t n ΔFS ΔPCS p) ∧
      SPComp.NoFail (smRealViewK M ini Sch t n ΔFS ΔPCS p) := fun p =>
    smSessView_pureNF (fun k => hini k p.2) Sch t n ΔFS ΔPCS _ p.1
  have hI : ∀ d, SPComp.IsPure (smIdealViewK M ini Sch t n ΔFS ΔPCS d) ∧
      SPComp.NoFail (smIdealViewK M ini Sch t n ΔFS ΔPCS d) := fun d =>
    smIdealView_pureNF (fun k => hini k d) Sch t n ΔFS ΔPCS
  have hXL := x3dhPair_seq_realizesSim G P (smRealViewK M ini Sch t n ΔFS ΔPCS) Leff hLeff hL
  have h := stack_realizes_FSCK_of (x3dhRealPair (K := K) G) (simProtPair G)
    (simProtPair_opaque G) x3dhFwd (simProtPair_isFwd G) (prekeySplit K S)
    (smRealViewK M ini Sch t n ΔFS ΔPCS) (smIdealViewK M ini Sch t n ΔFS ΔPCS) hR hI hXL
  intro ζ Z
  exact (h ζ Z).trans (add_le_add le_rfl (scBoundK_le_keyTermK M ini hM hini Sch t n ΔFS ΔPCS _))

end Stack

/-! ## The gated ACD ratchet at the signed-prekey pair -/

section ACD

open CatCrypt.Crypto.Assumptions CatCrypt.Crypto.PRPPRF CatCryptCore.Examples.CyclicGroupDDH

variable {S W : Type} [Field S] [Fintype S] [SampleableType W] (GX : DHGroup S W)
  {Gc : Type} [CG : CyclicGroup Gc] [DecidableEq Gc] {Sk : Type} [Fintype Sk] [Nonempty Sk]
  [Inhabited Sk] {RK Sa Wd Ct V : Type} [SampleableType Wd] [SampleableType Ct] [Fintype RK]
  [Nonempty RK] [Inhabited RK] [DecidableEq RK] [Fintype Sa] [Nonempty Sa]

/-- **The efficient layer of the gated ACD ratchet at the signed-prekey pair**: at the key `k`
and the public value `w` of the prekey, the real session view of the gated double ratchet over
`dhCKAPre decE (encW w)`, with the corruption answers read through `dhPreOpen`. It reads the
prekey only through its public value. -/
noncomputable def smPreView (decE : Sk → CG.Exp) (encW : W → Gc)
    (R : PRGDef (RK × Gc) (RK × Sa)) (F : PRGDef Sa (Wd × Sa)) (D : AEADDef Wd Ct)
    (Sch : Gc → OracleAdv (SMQuery Wd) (SMSchemeAns Gc Ct (Option (SMPartySt (Gc × Sk) RK Sa))) V)
    (t n ΔFS ΔPCS : ℕ) (p : RK × W) : SPComp V :=
  smSessView (acdSM (dhCKAPre decE (encW p.2)) R F D).gateB
    (gateIni (acdIni (Sa := Sa) (dhCKAPre decE (encW p.2))))
    (fun T => (Sch T).mapQueryAnswer id
      (SMSchemeAns.map id id (Option.map (SMPartySt.mapCk dhPreOpen))))
    t n ΔFS ΔPCS (fun _ => false) p.1

omit [SampleableType W] [DecidableEq Gc] [Inhabited RK] [DecidableEq RK] [Fintype Sa]
  [Nonempty Sa] in
/-- The efficient layer never fails. -/
theorem smPreView_noFail (decE : Sk → CG.Exp) (encW : W → Gc)
    (R : PRGDef (RK × Gc) (RK × Sa)) (F : PRGDef Sa (Wd × Sa)) (D : AEADDef Wd Ct)
    (Sch : Gc → OracleAdv (SMQuery Wd) (SMSchemeAns Gc Ct (Option (SMPartySt (Gc × Sk) RK Sa))) V)
    (t n ΔFS ΔPCS : ℕ) (p : RK × W) :
    SPComp.NoFail (smPreView decE encW R F D Sch t n ΔFS ΔPCS p) := by
  have hC : PureNF (dhCKAPre decE (encW p.2)).init := by
    simp only [dhCKAPre]
    refine PureNF.bind (pureNF_sample Sk) fun x => ?_
    exact pureNF_pure _
  exact (smSessView_pureNF (fun k => (acdIni_pureNF (C := dhCKAPre decE (encW p.2))
    hC k).bind fun _ => pureNF_pure _)
    _ t n ΔFS ΔPCS _ p.1).2

/-- **The bound of the gated ACD ratchet at the signed-prekey pair** of `x₀` at an adversary `A`
against the ungated scheme: the right-hand side of `sm_dh_corrupt_advantage_le_pair`. -/
noncomputable def smPairBound (decE : Sk → CG.Exp) (c : SamplerCert CG.Exp)
    (R : PRGDef (RK × Gc) (RK × Sa)) (F : PRGDef Sa (Wd × Sa)) (D : AEADDef Wd Ct)
    (ΔFS ΔPCS : ℕ) (x₀ : Sk) (A : SMCorruptAdv (Gc × Sk) Gc RK Sa Wd Ct) : ℝ≥0∞ :=
  (∑ b : Bool, PRFPRNG_Advantage R
      (smcRootRedFirst (dhCKAOf Gc decE) R F D ΔFS ΔPCS b (dhPairInit decE x₀) A.first) +
    FSAEAD_Corrupt_Advantage F D
      (smcFSRed (dhCKAOf Gc decE) R F D ΔFS ΔPCS (PMF.pure (dhPairInit decE x₀)) A.first)) +
  (∑ b : Bool, DDH_Advantage Gc
      (ckaCorruptDDHRedAt decE x₀ ΔFS ΔPCS (smcCKARed (Rand := Sk) R F D b A.later)) +
    8 * c.δ +
    ∑ b : Bool, PRFPRNG_Advantage R
      (smcRootRed (dhCKAOf Gc decE) R F D ΔFS ΔPCS b (PMF.pure (dhPairInit decE x₀)) A.later) +
    FSAEAD_Corrupt_Advantage F D
      (smcFSRed (dhCKAOf Gc decE) R F D ΔFS ΔPCS (PMF.pure (dhPairInit decE x₀)) A.later))

omit [Inhabited RK] in
/-- **The corruption advantage of the gated ACD ratchet at the signed-prekey pair**: the
advantage of `A` is at most `smPairBound` at the gated adversary `A.gateB` read as an adversary of
`sm_corrupt_game`. -/
theorem gateB_corruptAdvantage_le_pair (decE : Sk → CG.Exp) (c : SamplerCert CG.Exp)
    (hμ : c.μ = (SDistr.uniform Sk).bind fun x => SDistr.pure (decE x))
    (hν : c.ν = SDistr.uniform CG.Exp) (R : PRGDef (RK × Gc) (RK × Sa))
    (F : PRGDef Sa (Wd × Sa)) (D : AEADDef Wd Ct) {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS)
    (hPCS : 2 ≤ ΔPCS) (x₀ : Sk) (A : SMSchemeAdv Gc Wd Ct (Option (SMPartySt (Gc × Sk) RK Sa))) :
    (acdSM ((dhCKAOf Gc decE).atInit (dhPairInit decE x₀)) R F D).gateB.corruptAdvantage
        ΔFS ΔPCS A ≤
      smPairBound decE c R F D ΔFS ΔPCS x₀ A.gateB.toSM := by
  have hg : (acdSM ((dhCKAOf Gc decE).atInit (dhPairInit decE x₀)) R F D).gateB.corruptAdvantage
      ΔFS ΔPCS A =
      (acdSM ((dhCKAOf Gc decE).atInit (dhPairInit decE x₀)) R F D).corruptAdvantage ΔFS ΔPCS
        A.gateB := by
    simp only [SMScheme.corruptAdvantage, smSchemeGame_gateB]
  rw [hg, acdSM_corruptAdvantage_eq ((dhCKAOf Gc decE).atInit (dhPairInit decE x₀))
    (J := dhKeyRel Gc decE) ⟨(dhCKAOf_correct Gc decE).key, (dhCKAOf_correct Gc decE).next⟩
    (PMF.pure (dhPairInit decE x₀)) (liftPMF_pure _) (fun i hi => by
      rw [PMF.support_pure, Set.mem_singleton_iff] at hi
      subst hi
      rfl)]
  exact sm_dh_corrupt_advantage_le_pair decE c hμ hν R F D hFS hPCS x₀ _

variable [Inhabited S]

/-- **The Signal stack over the gated double ratchet of ACD at the signed-prekey pair realizes
secure messaging with corruption** (genuine UC): `signal_stack_realizes_FSM_prekey` at the
schemes `(acdSM ((dhCKAOf Gc decE).atInit (dhPairInit decE (ι x₀))) R F D).gateB`, keyed by the
root key through `gateIni (acdIniPair …)`, for a map `ι` of the X3DH prekey secret to the secret
key of the ratchet and a map `encW` of the X3DH public values to the ratchet group with
`g ^ decE (ι x) = encW (GX.pub x)`.

*Ideal functionality.* `F_SMK` at these schemes: completed sessions have the ideal view of the
gated ratchet at the prekey pair of their datum.

*Real world.* X3DH with the datum followed by the ratchet layer whose first epoch starts from the
prekey pair of the responder (Signal's `RatchetInitAlice` / `RatchetInitBob`).

*Simulator.* `chanSim (simProtPair GX) x3dhFwd`.

*Bound.* `fsmBoundPair` with the efficient layer `smPreView` (`smSessView_pair_eq_pre`) and, at
each datum `x₀`, the bound `smPairBound` at `ι x₀` of `sm_dh_corrupt_advantage_le_pair`: PRF-PRNG
advantages of the root KDF, FS-AEAD advantages and DDH advantages of explicit reductions, and
`8 c.δ`, for `2 ≤ ΔFS` and `2 ≤ ΔPCS`. -/
theorem signal_stack_realizes_FSM_acd_prekey (P : Finset PartyId) (decE : Sk → CG.Exp)
    (c : SamplerCert CG.Exp)
    (hμ : c.μ = (SDistr.uniform Sk).bind fun x => SDistr.pure (decE x))
    (hν : c.ν = SDistr.uniform CG.Exp) (ι : S → Sk) (encW : W → Gc)
    (hpub : ∀ x, CG.pow (decE (ι x)) = encW (GX.pub x)) (R : PRGDef (RK × Gc) (RK × Sa))
    (F : PRGDef Sa (Wd × Sa)) (D : AEADDef Wd Ct)
    (Sch : Gc → OracleAdv (SMQuery Wd) (SMSchemeAns Gc Ct (Option (SMPartySt (Gc × Sk) RK Sa))) V)
    {t n ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 2 ≤ ΔPCS) :
    RealizesSim ((x3dhRealPair (K := RK) GX).seq (smCorruptLayerK
        (fun x₀ => (acdSM ((dhCKAOf Gc decE).atInit (dhPairInit decE (ι x₀))) R F D).gateB)
        (fun k x₀ => gateIni (acdIniPair (Sa := Sa) (dhCKAOf Gc decE) (dhPairInit decE (ι x₀))) k)
        Sch t n ΔFS ΔPCS))
      (F_SMK (fun x₀ => (acdSM ((dhCKAOf Gc decE).atInit (dhPairInit decE (ι x₀))) R F D).gateB)
        (fun k x₀ => gateIni (acdIniPair (Sa := Sa) (dhCKAOf Gc decE) (dhPairInit decE (ι x₀))) k)
        Sch t n ΔFS ΔPCS)
      (chanSim (simProtPair (K := RK) GX) x3dhFwd)
      (fsmBoundPair GX P
        (fun x₀ => (acdSM ((dhCKAOf Gc decE).atInit (dhPairInit decE (ι x₀))) R F D).gateB)
        (fun k x₀ => gateIni (acdIniPair (Sa := Sa) (dhCKAOf Gc decE) (dhPairInit decE (ι x₀))) k)
        (fun x₀ A => smPairBound decE c R F D ΔFS ΔPCS (ι x₀) A.gateB.toSM)
        Sch t n ΔFS ΔPCS (smPreView decE encW R F D Sch t n ΔFS ΔPCS)
        (smPreView_noFail decE encW R F D Sch t n ΔFS ΔPCS)) := by
  have hM : ∀ x₀ : S,
      (acdSM ((dhCKAOf Gc decE).atInit (dhPairInit decE (ι x₀))) R F D).gateB.init =
        SPComp.bind (SPComp.sample RK) fun k =>
          gateIni (acdIniPair (Sa := Sa) (dhCKAOf Gc decE) (dhPairInit decE (ι x₀))) k := by
    intro x₀
    simp only [SMScheme.gateB]
    rw [acdSM_init_eq _ R F D (SPComp.pure_isPure _), SPComp.bind_assoc]
    rfl
  have hini : ∀ (k : RK) (x₀ : S), PureNF
      (gateIni (acdIniPair (Sa := Sa) (dhCKAOf Gc decE) (dhPairInit decE (ι x₀))) k) :=
    fun k x₀ => (acdIni_pureNF (pureNF_pure _) k).bind fun _ => pureNF_pure _
  have hL : ∀ k x₀, smRealViewK
      (fun x₀ => (acdSM ((dhCKAOf Gc decE).atInit (dhPairInit decE (ι x₀))) R F D).gateB)
      (fun k x₀ => gateIni (acdIniPair (Sa := Sa) (dhCKAOf Gc decE) (dhPairInit decE (ι x₀))) k)
      Sch t n ΔFS ΔPCS (k, x₀) = smPreView decE encW R F D Sch t n ΔFS ΔPCS (k, GX.pub x₀) := by
    intro k x₀
    rw [smRealViewK, smRealView, smPreView, ← hpub]
    exact smSessView_pair_eq_pre decE R F D Sch t n ΔFS ΔPCS _ (ι x₀) k
  intro ζ Z
  exact (signal_stack_realizes_FSM_prekey GX P _ _ hM hini Sch t n ΔFS ΔPCS _
    (smPreView_noFail decE encW R F D Sch t n ΔFS ΔPCS) hL ζ Z).trans
    (fsmBoundPair_mono GX P _ _ (fun x₀ A => gateB_corruptAdvantage_le_pair decE c hμ hν R F D
      hFS hPCS (ι x₀) A) Sch t n ΔFS ΔPCS _ _ ζ Z)

end ACD

end CatCrypt.Crypto.Messaging.SignalStackSMPrekey
