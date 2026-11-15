/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SMIDACD
public import CatCryptCore.Crypto.Messaging.SMIDSidecar
public import CatCryptCore.Crypto.Messaging.SMAuthFSInt
import CatCryptCore.Tactics.AutoDispatchExt

/-!
# Integrity of the ACD construction with headers

The integrity advantage of a scheme with headers and immediate decryption (`SMIDScheme`) as a
sum of forgery events in the game with decryption from the log, and, for the ACD construction
with headers `acdIDSM`, the CKA hop and the root hop of each forgery event, after the hops of the
authenticity game (`CatCryptCore.Crypto.Messaging.SMAuth`,
`CatCryptCore.Crypto.Messaging.SMAuthRoot`).

## Forgeries in the game with decryption from the log

The real game and the game with decryption from the log agree until a delivery whose real
decryption differs from the answer from the log. For an adversary asking at most `N` queries,
every delivery is into an epoch below `N`, so (`SMIDScheme.intAdvantage_le_sum_logBad`)

  `Adv_int(A) ≤ ∑_{k < N} Pr[smIDLogBadGame k A]`,

where `smIDLogBadGame k A` is the probability of a forgery at the epoch `k` in the game with
decryption from the log in every epoch. In that game the invariant `ACDIDInv` of `acdIDSM`
holds at every state.

## The hop games beside the base

A state of the game over `acdIDSM` is joined (`acdIDJoin`) from a state of the
secure-messaging game of the base (`SMSt`, with the root output in transit) and the bookkeeping
`ACDIDX` of the parties beside their base states: public values, counters, received epochs and
stored keys. Over the base, the AEAD is `aeadComapAD D dec`, so that the sender's associated
data `enc h ad` reach `D` as `(ad, h)` (`acdIDSM_scheme_step`). The hop game
`acdIDHopGame … k root A` runs the oracle of the game with decryption from the log over these
states, with the root step `root` at the opening of the epoch `k`, the flag of a forgery at the
epoch `k`, and the cut at the first answered corruption with the epoch `k` in its window. At the
real root step it is the truncated forgery game (`acdIDSM_logTruncGame_eq_hop`).

## The CKA and root hops

The CKA reduction `acdIDCKARed` sets the CKA challenge at the epoch `k` and simulates the hop
game from the receiving chains it keeps; its CKA games are the hop games with the root steps
`ckaHopRoot R idealK` (`acdIDHopGame_eq_cka`). The PRF-PRNG reduction `acdIDRootRed` asks the
root step at the opening of the epoch `k` to the `prf` oracle; its PRF-PRNG games are the hop
games with the root KDF on a uniform key and with a uniform root output
(`acdIDRoot_real_eq`, `acdIDRoot_ideal_eq`). Hence (`acdIDSM_intAdvantage_le_unifRoot`)

  `Adv_int(A) ≤ ∑_{k < N} (Adv_CKA(acdIDCKARed k A) + Adv_PRF-PRNG(acdIDRootRed k A) +
    Pr[acdIDHopGame k unifRoot A])`.

## Main definitions

* `smIDFlagsOracle`, `smIDFlagsRun` — the oracle with a flag per epoch
* `smIDBelowOracle`, `smIDBelowRun` — the oracle with the flag of a forgery below a horizon
* `smIDLogBadGame`, `smIDLogTruncGame` — the forgery event at an epoch in the game with
  decryption from the log, and its truncation at the corruption of the epoch
* `ACDIDSt.withBase`, `ACDIDX`, `acdIDJoin`, `acdIDAns`, `acdIDXUpd` — the bookkeeping beside
  the base
* `acdIDRcvSt`, `acdIDDeliver` — the delivery beside the base
* `ACDIDHopSt`, `acdIDHopStep`, `acdIDHopOracle`, `acdIDHopGame` — the hop games
* `acdIDCKAFwd`, `acdIDCKAImpl`, `acdIDCKATree`, `acdIDCKARed` — the CKA reduction
* `acdIDRootImpl`, `acdIDRootTree`, `acdIDRootRed` — the PRF-PRNG reduction

## Main results

* `prTrue_bind_bind_any_le_sum` — the union bound through the draws of a game
* `SMIDScheme.intAdvantage_le_sum_logBad` — the first bound above
* `smIDLogTruncGame_eq` — the truncated forgery game is the forgery game
* `acdIDSM_scheme_step`, `acdIDDeliver_join` — the oracle over `acdIDSM` beside the base
* `acdIDSM_logTruncGame_eq_hop` — the truncated forgery game is the hop game at the real root
* `acdIDHopGame_eq_cka`, `acdIDSM_logTruncGame_le_cka` — the CKA hop
* `acdIDRoot_real_eq`, `acdIDRoot_ideal_eq`, `acdIDHopGame_le_root` — the root hop
* `acdIDSM_intAdvantage_le_unifRoot` — the second bound above
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
open scoped ENNReal

/-! ## The union bound through the draws of a game -/

/-- **The union bound through the draws of a game.** For a game that draws `t` from `T` and `i`
from `I` and then outputs whether one of the flags `F x k`, `k < n`, of an outcome `x` of
`μ t i` is set, the probability of the output is at most the sum over `k < n` of the
probabilities of the flag `k`. -/
theorem prTrue_bind_bind_any_le_sum {τ X β : Type} (T : PMF τ) (I : SPComp X)
    (μ : τ → X → PMF β) (F : β → ℕ → Bool) (n : ℕ) :
    prTrue (SPComp.bind (liftPMF T) fun t => SPComp.bind I fun i =>
        liftPMF ((μ t i).map fun x => (List.range n).any (F x))) Heap.empty ≤
      ∑ k ∈ Finset.range n, prTrue (SPComp.bind (liftPMF T) fun t => SPComp.bind I fun i =>
        liftPMF ((μ t i).map fun x => F x k)) Heap.empty := by
  have hz : ∀ {α : Type} (c : SPComp α) (k : α → SPComp Bool) (h : Heap),
      (∀ a h', prTrue (k a) h' = 0) → prTrue (SPComp.bind c k) h = 0 := by
    intro α c k h hk
    rw [ForkingLemma.prTrue_bind_eq_weighted]
    exact ENNReal.tsum_eq_zero.mpr fun p => by rcases p with _ | ⟨a, h'⟩ <;> simp [hk]
  induction n with
  | zero =>
    simp only [List.range_zero, List.any_nil, Finset.range_zero, Finset.sum_empty,
      nonpos_iff_eq_zero]
    exact hz _ _ _ fun t h' => hz _ _ _ fun i h'' => by simp [PRPPRF.prTrue_liftPMF_map]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    refine le_trans ?_ (add_le_add ih le_rfl)
    refine ForkingLemma.prTrue_bind_le_add _ _ _ _ _ fun t h' => ?_
    refine ForkingLemma.prTrue_bind_le_add _ _ _ _ _ fun i h'' => ?_
    simp only [PRPPRF.prTrue_liftPMF_map]
    refine le_trans (MeasureTheory.measure_mono ?_) (MeasureTheory.measure_union_le _ _)
    intro x hx
    simp only [List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_eq_true, Set.mem_ofPred_eq] at hx
    simpa using hx

/-! ## Forgeries in the game with decryption from the log -/

section LogBad

variable {St Pub Rand W Ct Leak Hdr K : Type} [Fintype Rand] [Nonempty Rand] [DecidableEq Pub]
  [DecidableEq W] [DecidableEq Hdr] [DecidableEq Ct]

/-- The oracle `smIDOracleAt` with a flag for each epoch, set at a forgery at that epoch. -/
noncomputable def smIDFlagsOracle (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ΔFS ΔPCS t : ℕ)
    (idealC : Bool) (idealD : ℕ → Bool)
    (s : (SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) × (ℕ → Bool)) (d : SMIDQuery W Hdr Ct) :
    PMF (SMIDAns Pub Hdr Ct Leak W × ((SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) × (ℕ → Bool))) :=
  (smIDOracleAt M ΔFS ΔPCS t idealC idealD s.1 d).map fun y =>
    (y.1, (y.2, fun k => s.2 k || smIDBadAt M ΔFS ΔPCS k s.1 d))

/-- The run of `A` against `smIDFlagsOracle` at the challenge epoch `t` from the initial state
`i` of the scheme, with every flag cleared. -/
noncomputable def smIDFlagsRun (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ΔFS ΔPCS : ℕ)
    (idealC : Bool) (idealD : ℕ → Bool) (A : SMIDAdv Pub W Hdr Ct Leak) (t : ℕ)
    (i : Pub × St × St) :
    PMF (Bool × ((SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) × (ℕ → Bool))) :=
  OracleAdv.run (smIDFlagsOracle M ΔFS ΔPCS t idealC idealD) (A.play t i.1)
    ((SMSchemeSt.init i, SMIDAux.init i.1), fun _ => false)

/-- The oracle `smIDOracleAt` with a flag that is set at a forgery at an epoch below `N`. -/
noncomputable def smIDBelowOracle (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (ΔFS ΔPCS t : ℕ) (idealC : Bool) (idealD : ℕ → Bool) (N : ℕ)
    (s : (SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) × Bool) (d : SMIDQuery W Hdr Ct) :
    PMF (SMIDAns Pub Hdr Ct Leak W × ((SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) × Bool)) :=
  (smIDOracleAt M ΔFS ΔPCS t idealC idealD s.1 d).map fun y =>
    (y.1, (y.2, s.2 || (List.range N).any fun k => smIDBadAt M ΔFS ΔPCS k s.1 d))

/-- The run of `A` against `smIDBelowOracle` at the challenge epoch `t` from the initial state
`i` of the scheme. -/
noncomputable def smIDBelowRun (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ΔFS ΔPCS : ℕ)
    (idealC : Bool) (idealD : ℕ → Bool) (N : ℕ) (A : SMIDAdv Pub W Hdr Ct Leak) (t : ℕ)
    (i : Pub × St × St) :
    PMF (Bool × ((SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) × Bool)) :=
  OracleAdv.run (smIDBelowOracle M ΔFS ΔPCS t idealC idealD N) (A.play t i.1)
    ((SMSchemeSt.init i, SMIDAux.init i.1), false)

/-- **The forgery event at the epoch `k` with decryption from the log**: the game that runs `A`
with decryption from the log in every epoch and outputs whether a forgery at the epoch `k` was
delivered. -/
noncomputable def smIDLogBadGame (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ΔFS ΔPCS k : ℕ)
    (A : SMIDAdv Pub W Hdr Ct Leak) : SPComp Bool :=
  SPComp.bind (liftPMF A.tStar) fun t => SPComp.bind M.init fun i =>
    liftPMF ((smIDFlagRun M ΔFS ΔPCS false (fun _ => true) k A t i).map fun x => x.2.2)

/-- The flag of the epoch `k` of the run with a flag per epoch is the flag of the run with the
flag of the epoch `k`. -/
theorem smIDFlagsRun_map_flag (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ΔFS ΔPCS : ℕ)
    (idealC : Bool) (idealD : ℕ → Bool) (k : ℕ) (A : SMIDAdv Pub W Hdr Ct Leak) (t : ℕ)
    (i : Pub × St × St) :
    (smIDFlagsRun M ΔFS ΔPCS idealC idealD A t i).map (fun x => x.2.2 k) =
      (smIDFlagRun M ΔFS ΔPCS idealC idealD k A t i).map fun x => x.2.2 := by
  have h := OracleAdv.run_map_state (smIDFlagsOracle M ΔFS ΔPCS t idealC idealD)
    (smIDFlagOracle M ΔFS ΔPCS t idealC idealD k) (fun s => (s.1, s.2 k))
    (fun s d => by rw [smIDFlagsOracle, PMF.map_comp]; rfl) (A.play t i.1)
    ((SMSchemeSt.init i, SMIDAux.init i.1), fun _ => false)
  rw [smIDFlagRun, ← h, PMF.map_comp]
  rfl

/-- The flag of a forgery below `N` of the run with a flag per epoch is the flag of the run
with the flag of a forgery below `N`. -/
theorem smIDFlagsRun_map_below (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ΔFS ΔPCS : ℕ)
    (idealC : Bool) (idealD : ℕ → Bool) (N : ℕ) (A : SMIDAdv Pub W Hdr Ct Leak) (t : ℕ)
    (i : Pub × St × St) :
    (smIDFlagsRun M ΔFS ΔPCS idealC idealD A t i).map
        (fun x => (List.range N).any x.2.2) =
      (smIDBelowRun M ΔFS ΔPCS idealC idealD N A t i).map fun x => x.2.2 := by
  have h := OracleAdv.run_map_state (smIDFlagsOracle M ΔFS ΔPCS t idealC idealD)
    (smIDBelowOracle M ΔFS ΔPCS t idealC idealD N) (fun s => (s.1, (List.range N).any s.2))
    (fun s d => by
      rw [smIDFlagsOracle, smIDBelowOracle, PMF.map_comp]
      congr 1
      funext y
      simp only [Function.comp_apply, Prod.map, id_eq, Prod.mk.injEq, true_and]
      grind)
    (A.play t i.1) ((SMSchemeSt.init i, SMIDAux.init i.1), fun _ => false)
  rw [smIDBelowRun, show (false : Bool) = (List.range N).any fun _ => false by simp, ← h,
    PMF.map_comp]
  rfl

/-- The output of the run with the flag of a forgery below `N` is the output of the run against
`smIDOracleAt`. -/
theorem smIDBelowRun_map_fst (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ΔFS ΔPCS : ℕ)
    (idealC : Bool) (idealD : ℕ → Bool) (N : ℕ) (A : SMIDAdv Pub W Hdr Ct Leak) (t : ℕ)
    (i : Pub × St × St) :
    (smIDBelowRun M ΔFS ΔPCS idealC idealD N A t i).map Prod.fst =
      (OracleAdv.run (smIDOracleAt M ΔFS ΔPCS t idealC idealD) (A.play t i.1)
        (SMSchemeSt.init i, SMIDAux.init i.1)).map Prod.fst := by
  have h := OracleAdv.run_map_state (smIDBelowOracle M ΔFS ΔPCS t idealC idealD N)
    (smIDOracleAt M ΔFS ΔPCS t idealC idealD) Prod.fst
    (fun s d => by rw [smIDBelowOracle, PMF.map_comp]; exact PMF.map_id _) (A.play t i.1)
    ((SMSchemeSt.init i, SMIDAux.init i.1), false)
  dsimp only at h
  rw [smIDBelowRun, ← h, PMF.map_comp]
  rfl

omit [Fintype Rand] [Nonempty Rand] in
/-- Without a forgery below `N`, real decryption below `N` and decryption from the log answer a
delivery alike. -/
theorem smIDDeliver_agree_below (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ΔFS ΔPCS N : ℕ)
    (s : SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) (p : CKAParty) (h : Hdr) (ad : W) (c : Ct)
    (hb : ∀ k < N, smIDBadAt M ΔFS ΔPCS k s (.deliver p h ad c) = false) :
    smIDDeliver M ΔFS ΔPCS (fun e => decide (N ≤ e)) s p h ad c =
      smIDDeliver M ΔFS ΔPCS (fun _ => true) s p h ad c := by
  unfold smIDDeliver
  cases he : s.2.epochOf (ckaShadow s.1.ck) p (M.hdrPub h) with
  | none => rfl
  | some e =>
    dsimp only
    by_cases hN : N ≤ e
    · simp [hN]
    · have hb' := hb e (by omega)
      simp only [smIDBadAt, he, decide_true, Bool.true_and] at hb'
      by_cases hsafe : s.2.safe ΔFS ΔPCS p e (M.hdrPos h) = true
      · simp only [hsafe, ite_true]
        cases hr : M.rkey (s.1.ck.st p) h with
        | none => rfl
        | some y =>
          simp only [hsafe, hr, Bool.true_and, bne_eq_false_iff_eq] at hb'
          simp [hN, hb']
      · simp [hsafe]

/-- The flag of `smIDBelowOracle` stays set. -/
theorem smIDBelowOracle_sticky (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ΔFS ΔPCS t : ℕ)
    (idealC : Bool) (idealD : ℕ → Bool) (N : ℕ) (s : SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct)
    (d : SMIDQuery W Hdr Ct) (r : SMIDAns Pub Hdr Ct Leak W)
    (s' : SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) :
    smIDBelowOracle M ΔFS ΔPCS t idealC idealD N (s, true) d (r, (s', false)) = 0 := by
  refine (PMF.apply_eq_zero_iff _ _).mpr ?_
  simp [smIDBelowOracle]

/-- Real decryption below `N` and decryption from the log agree on every transition that leaves
the flag of a forgery below `N` cleared. -/
theorem smIDBelowOracle_agree (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ΔFS ΔPCS t : ℕ)
    (idealC : Bool) (N : ℕ) (s : (SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) × Bool)
    (d : SMIDQuery W Hdr Ct) (r : SMIDAns Pub Hdr Ct Leak W)
    (s' : SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) :
    smIDBelowOracle M ΔFS ΔPCS t idealC (fun e => decide (N ≤ e)) N s d (r, (s', false)) =
      smIDBelowOracle M ΔFS ΔPCS t idealC (fun _ => true) N s d (r, (s', false)) := by
  by_cases hb : (s.2 || (List.range N).any fun k => smIDBadAt M ΔFS ΔPCS k s.1 d) = true
  · rw [(PMF.apply_eq_zero_iff _ _).mpr, (PMF.apply_eq_zero_iff _ _).mpr] <;>
      simp [smIDBelowOracle, hb]
  · cases d with
    | sm q => rfl
    | deliver p h ad c =>
      simp only [Bool.or_eq_true, not_or, List.any_eq_true, List.mem_range, not_exists,
        not_and] at hb
      have hb' : ∀ k < N, smIDBadAt M ΔFS ΔPCS k s.1 (.deliver p h ad c) = false :=
        fun k hk => by simpa using hb.2 k hk
      simp only [smIDBelowOracle, smIDOracleAt]
      rw [smIDDeliver_agree_below M ΔFS ΔPCS N s.1 p h ad c hb']

/-- **Integrity from the forgery events with decryption from the log.** For an adversary asking
at most `N` queries, the integrity advantage is at most the sum over the epochs `k < N` of the
probabilities of a forgery at the epoch `k` in the game with decryption from the log. -/
theorem SMIDScheme.intAdvantage_le_sum_logBad (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (ΔFS ΔPCS N : ℕ) (A : SMIDAdv Pub W Hdr Ct Leak)
    (hA : ∀ t pub, (A.play t pub).IsQueryBound N) :
    M.intAdvantage ΔFS ΔPCS A ≤
      ∑ k ∈ Finset.range N, prTrue (smIDLogBadGame M ΔFS ΔPCS k A) Heap.empty := by
  have h0 : smIDGame M ΔFS ΔPCS false false A =
      smIDGameAt M ΔFS ΔPCS false (fun e => decide (N ≤ e)) A :=
    smIDGameAt_congr_of_isQueryBound M ΔFS ΔPCS false (fun e he => by simp; omega) A hA
  have hg : ∀ idealD, smIDGameAt M ΔFS ΔPCS false idealD A =
      SPComp.bind (liftPMF A.tStar) fun t => SPComp.bind M.init fun i =>
        liftPMF ((smIDBelowRun M ΔFS ΔPCS false idealD N A t i).map Prod.fst) := by
    intro idealD
    simp only [smIDGameAt, smIDBelowRun_map_fst]
  unfold SMIDScheme.intAdvantage
  rw [h0, smIDGame, hg, hg]
  refine (advantage_bind_liftPMF_le_flag _ _
    (fun t i => smIDBelowRun M ΔFS ΔPCS false (fun e => decide (N ≤ e)) N A t i)
    (fun t i => smIDBelowRun M ΔFS ΔPCS false (fun _ => true) N A t i)
    fun t i a s => OracleAdv.run_apply_flag_false_eq _ _
      (smIDBelowOracle_sticky M ΔFS ΔPCS t false _ N)
      (smIDBelowOracle_sticky M ΔFS ΔPCS t false _ N)
      (smIDBelowOracle_agree M ΔFS ΔPCS t false N) _ _ a s).trans ?_
  simp only [← smIDFlagsRun_map_below]
  refine (prTrue_bind_bind_any_le_sum A.tStar M.init
    (fun t i => smIDFlagsRun M ΔFS ΔPCS false (fun _ => true) A t i) (fun x => x.2.2) N).trans
    (le_of_eq ?_)
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [smIDLogBadGame, smIDFlagsRun_map_flag]

/-- **The truncated forgery game at the epoch `k` with decryption from the log**:
`smIDLogBadGame` with the oracle truncated at the first corruption that falls in the window of
the epoch `k`. -/
noncomputable def smIDLogTruncGame (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (ΔFS ΔPCS k : ℕ) (A : SMIDAdv Pub W Hdr Ct Leak) : SPComp Bool :=
  SPComp.bind (liftPMF A.tStar) fun t => SPComp.bind M.init fun i =>
    liftPMF ((OracleAdv.run (smIDTruncOracle M ΔFS ΔPCS t false (fun _ => true) k)
      (A.play t i.1) ((SMSchemeSt.init i, SMIDAux.init i.1), false)).map fun x => x.2.2)

/-- **Every forgery precedes the corruption of its epoch**, with decryption from the log: the
truncated forgery game at the epoch `k` is the forgery game at the epoch `k`. -/
theorem smIDLogTruncGame_eq (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ΔFS ΔPCS k : ℕ)
    (A : SMIDAdv Pub W Hdr Ct Leak) :
    smIDLogTruncGame M ΔFS ΔPCS k A = smIDLogBadGame M ΔFS ΔPCS k A := by
  unfold smIDLogTruncGame smIDLogBadGame smIDFlagRun
  refine congrArg _ (funext fun t => congrArg _ (funext fun i => congrArg _ ?_))
  refine OracleAdv.run_map_eq_of_agree_until_stop _ _
    (fun s : (SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) × Bool =>
      s.1.2.epochSafe ΔFS ΔPCS k = false) (fun s => s.2) ?_ ?_ ?_ _ _
  · intro s d hs
    simp [smIDTruncOracle, hs]
  · intro s d hs x hx
    simp only [smIDTruncOracle, hs, Bool.false_eq_true, ite_false, PMF.support_pure,
      Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨hs, rfl⟩
  · exact fun s d hs => smIDFlagOracle_stopped M ΔFS ΔPCS t false _ k s hs d

end LogBad

/-! ## The bookkeeping of the ACD construction with headers beside the base -/

section Join

variable {Sc Msg Key Rand RK Sa W Ct : Type}

/-- The state `x` of the ACD construction with headers with the base state `b` in place of its
own. -/
def ACDIDSt.withBase {Sc' RK' : Type} (x : ACDIDSt Sc' RK' Sa Msg W) (b : SMPartySt Sc RK Sa) :
    ACDIDSt Sc RK Sa Msg W :=
  ⟨b, x.pubS, x.ns, x.ep, x.er, x.nr, x.rpubs, x.store⟩

/-- The bookkeeping of the parties of `acdIDSM` beside their base states, with the number `PN`
of the public value in transit. It is kept over the trivial base type; the base state inside is
not read: `acdIDJoin` replaces it. -/
abbrev ACDIDX (Sa Msg W : Type) := (CKAParty → ACDIDSt Unit Unit Sa Msg W) × ℕ

/-- The header of the next ciphertext of party `p`. -/
def acdIDHdr (X : ACDIDX Sa Msg W) (p : CKAParty) : ACDHdr Msg :=
  ((X.1 p).pubS, (X.1 p).ns)

/-- The state of the game over `acdIDSM` from the state `σ` of the game over the base and the
bookkeeping `X`. -/
def acdIDJoin (σ : SMSt Sc Msg RK Sa) (X : ACDIDX Sa Msg W) :
    SMSchemeSt (ACDIDSt Sc RK Sa Msg W) (Msg × ℕ) :=
  ⟨⟨fun p => (X.1 p).withBase (σ.toScheme.ck.st p), σ.ck.t, (σ.ck.msg, X.2)⟩, σ.loc.done⟩

/-- The answer of the game over `acdIDSM` from the answer of the game over the base, for a party
with the bookkeeping `x`. -/
def acdIDAns (x : ACDIDSt Unit Unit Sa Msg W) :
    SMAns Sc Msg RK Sa Ct → SMSchemeAns (Msg × ℕ) Ct (ACDIDLeak Sc RK Sa Msg W)
  | .none => .none
  | .msg T => .msg (T, x.ns)
  | .ct c => .ct c
  | .state γ rk snd rcv =>
    .state ⟨⟨γ, rk, snd, rcv⟩, x.pubS, x.ns, x.ep, x.er, x.nr, x.rpubs, x.lookup⟩

/-- The bookkeeping of party `p` after receiving the public value `(T, PN)` with the receiving
chain `rcv` of its closed receiving epoch. -/
def ACDIDSt.recvX (G : PRGDef Sa (W × Sa)) (x : ACDIDSt Sc RK Sa Msg W) (rcv : Option Sa)
    (T : Msg × ℕ) : ACDIDSt Sc RK Sa Msg W :=
  ⟨x.base, x.pubS, x.ns, x.ep + 1, x.ep + 1, 0, (x.ep + 1, T) :: x.rpubs,
    (if x.er = 0 then [] else
      (rcv.map fun sa => ACDIDSt.skipKeys G x.er sa x.nr (T.2 - x.nr)).getD []) ++ x.store⟩

/-- The bookkeeping after the query `q` with the answer `a` of the game over the base, from the
receiving chains `rcv`, the epoch counters `sh` and the CKA message `T₀` in transit. -/
def acdIDXUpd (G : PRGDef Sa (W × Sa)) (rcv : CKAParty → Option Sa) (sh : CKAGameSt Unit Unit)
    (T₀ : Msg) (X : ACDIDX Sa Msg W) : SMQuery W → SMAns Sc Msg RK Sa Ct → ACDIDX Sa Msg W
  | .ratchet p, .msg T => (Function.update X.1 p
      ⟨(X.1 p).base, (T, (X.1 p).ns), 0, (X.1 p).ep + 1, (X.1 p).er, (X.1 p).nr, (X.1 p).rpubs,
        (X.1 p).store⟩, (X.1 p).ns)
  | .recv p, _ => if sh.canRecv p then
      (Function.update X.1 p ((X.1 p).recvX G (rcv p) (T₀, X.2)), X.2) else X
  | .send p _, .ct _ => (Function.update X.1 p { X.1 p with ns := (X.1 p).ns + 1 }, X.2)
  | .chall p _, .ct _ => (Function.update X.1 p { X.1 p with ns := (X.1 p).ns + 1 }, X.2)
  | _, _ => X

/-- Two states of the game over a scheme are equal when their party states, epoch counters,
public values in transit and challenge flags are. -/
theorem SMSchemeSt.ext_of {St Pub : Type} {s s' : SMSchemeSt St Pub} (hst : s.ck.st = s'.ck.st)
    (ht : s.ck.t = s'.ck.t) (hm : s.ck.msg = s'.ck.msg) (hd : s.done = s'.done) : s = s' := by
  obtain ⟨⟨st, t, m⟩, d⟩ := s
  obtain ⟨⟨st', t', m'⟩, d'⟩ := s'
  simp_all

variable [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct] [Fintype RK]
  [Nonempty RK] [Inhabited Msg] [DecidableEq Msg]

/-- **The oracle over `acdIDSM` from the oracle over the base.** Under the invariant `ACDInv`,
each call of the corruption-game oracle over `acdIDSM` at a joined state is the call of
`smOracleOf` at the real root step over the base with the AEAD `aeadComapAD D dec`, on the query
with the header attached to the associated data, with the answer and the bookkeeping
completed. -/
theorem acdIDSM_scheme_step (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored : ℕ)
    (J : Sc → Sc → Prop) (ΔFS ΔPCS t : ℕ) (ideal : Bool) (σ : SMSt Sc Msg RK Sa)
    (X : ACDIDX Sa Msg W) (hs : ACDInv C R J σ) (q : SMQuery W) :
    smSchemeOracle (acdIDSM C R G D dec enc maxSkip maxStored).toSMScheme ΔFS ΔPCS t ideal
        (acdIDJoin σ X) q =
      (smOracleOf C R G (aeadComapAD D dec) ΔFS ΔPCS t ideal (realRoot R) σ
        (q.mapMsg fun m => (m.1, enc (acdIDHdr X q.party) m.2))).map
        fun y => (acdIDAns (X.1 q.party) y.1,
          acdIDJoin y.2 (acdIDXUpd G σ.loc.rcv (ckaShadow σ.ck) σ.ck.msg X q y.1)) := by
  cases q with
  | ratchet p =>
    simp only [smSchemeOracle, smOracleOf, realRoot, ite_self, PMF.pure_bind, SMQuery.mapMsg]
    by_cases hc : σ.ck.canSend p = true
    · have hc' : (acdIDJoin σ X).ck.canSend p = true := hc
      simp only [hc, hc', ite_true, PMF.map_bind, PMF.pure_map]
      refine congrArg _ (funext fun r => ?_)
      simp only [acdIDAns, acdIDXUpd, acdIDJoin, acdIDSM, acdIDBase, acdSMAD, CKAGameSt.sent]
      refine congrArg PMF.pure (Prod.ext rfl ?_)
      simp only [SMSchemeSt.mk.injEq, CKAGameSt.mk.injEq]
      refine ⟨⟨funext fun q => ?_, trivial, rfl⟩, rfl⟩
      by_cases hq : q = p
      · subst hq
        simp [SMSt.toScheme, ACDIDSt.withBase, SMLoc.opened]
      · simp [SMSt.toScheme, ACDIDSt.withBase, SMLoc.opened, Function.update_of_ne hq]
    · have hc' : (acdIDJoin σ X).ck.canSend p = false := Bool.eq_false_iff.mpr hc
      simp only [hc', Bool.false_eq_true, ite_false, PMF.pure_map, hc]
      rfl
  | recv p =>
    simp only [smSchemeOracle, smOracleOf, SMQuery.mapMsg]
    by_cases hc : σ.ck.canRecv p = true
    · have hc' : (acdIDJoin σ X).ck.canRecv p = true := hc
      simp only [hc, hc', ite_true, PMF.pure_map, SMLoc.received, (hs.recv p hc).1]
      refine congrArg PMF.pure (Prod.ext rfl (SMSchemeSt.ext_of ?_ rfl
        (by simp [acdIDXUpd, hc, acdIDJoin, CKAGameSt.recvd]) rfl))
      funext q
      by_cases hq : q = p
      · subst hq
        simp [acdIDXUpd, hc, acdIDJoin, acdIDSM, acdIDBase, acdSMAD, CKAGameSt.recvd,
          SMLoc.recvY, SMSt.toScheme, ACDIDSt.withBase, ACDIDSt.recvX]
      · simp [acdIDXUpd, hc, acdIDJoin, CKAGameSt.recvd, SMLoc.recvY,
          SMSt.toScheme, ACDIDSt.withBase,
          Function.update_of_ne hq]
    · have hc' : (acdIDJoin σ X).ck.canRecv p = false := Bool.eq_false_iff.mpr hc
      simp only [hc, hc', Bool.false_eq_true, ite_false, PMF.pure_map, acdIDXUpd,
        ckaShadow_canRecv]
      rfl
  | send p m =>
    have ht : (acdIDJoin σ X).ck.t = σ.ck.t := rfl
    simp only [smSchemeOracle, smOracleOf, SMQuery.mapMsg, SMQuery.party, ht]
    cases hsnd : σ.loc.snd p with
    | none =>
      have h0 : (acdIDSM C R G D dec enc maxSkip maxStored).send ((acdIDJoin σ X).ck.st p) m =
          none := by
        simp [acdIDSM, acdIDBase, acdSMAD, acdIDJoin, SMSt.toScheme, ACDIDSt.withBase, hsnd]
      simp only [h0, PMF.pure_map]
      split_ifs <;> rfl
    | some sa =>
      by_cases hc : (ckaSender (σ.ck.t p) == p) = true
      · simp only [hc, ite_true, PMF.pure_map]
        have h1 : (acdIDSM C R G D dec enc maxSkip maxStored).send ((acdIDJoin σ X).ck.st p) m =
            some (⟨⟨σ.ck.st p, σ.loc.rk p, some (G.stretch sa).2, σ.loc.rcv p⟩, (X.1 p).pubS,
              (X.1 p).ns + 1, (X.1 p).ep, (X.1 p).er, (X.1 p).nr, (X.1 p).rpubs, (X.1 p).store⟩,
              D.encrypt (G.stretch sa).1 m.1 (dec (enc (acdIDHdr X p) m.2))) := by
          simp [acdIDSM, acdIDBase, acdSMAD, acdIDJoin,
              SMSt.toScheme, ACDIDSt.withBase, hsnd, acdIDHdr]
        simp only [h1]
        refine congrArg PMF.pure (Prod.ext rfl (SMSchemeSt.ext_of ?_ rfl rfl rfl))
        funext q
        by_cases hq : q = p
        · subst hq
          simp [acdIDXUpd, acdIDJoin, SMSchemeSt.upd, SMLoc.advanced,
              SMSt.toScheme, ACDIDSt.withBase]
        · simp [acdIDXUpd, acdIDJoin, SMSchemeSt.upd, SMLoc.advanced,
              SMSt.toScheme, ACDIDSt.withBase,
            Function.update_of_ne hq]
      · simp only [hc, Bool.false_eq_true, ite_false, PMF.pure_map]
        rfl
  | chall p m =>
    have ht : (acdIDJoin σ X).ck.t = σ.ck.t := rfl
    have hd : (acdIDJoin σ X).done = σ.loc.done := rfl
    simp only [smSchemeOracle, smOracleOf, SMQuery.mapMsg, SMQuery.party, ht, hd, challOk]
    cases hsnd : σ.loc.snd p with
    | none =>
      have h0 : (acdIDSM C R G D dec enc maxSkip maxStored).send ((acdIDJoin σ X).ck.st p) m =
          none := by
        simp [acdIDSM, acdIDBase, acdSMAD, acdIDJoin, SMSt.toScheme, ACDIDSt.withBase, hsnd]
      simp only [h0, PMF.pure_map]
      split_ifs <;> rfl
    | some sa =>
      by_cases hc : (!σ.loc.done && (ckaSender (σ.ck.t p) == p) && (σ.ck.t p == t)) = true
      · simp only [hc, ite_true, PMF.map_bind, PMF.pure_map]
        have h1 : (acdIDSM C R G D dec enc maxSkip maxStored).send ((acdIDJoin σ X).ck.st p) m =
            some (⟨⟨σ.ck.st p, σ.loc.rk p, some (G.stretch sa).2, σ.loc.rcv p⟩, (X.1 p).pubS,
              (X.1 p).ns + 1, (X.1 p).ep, (X.1 p).er, (X.1 p).nr, (X.1 p).rpubs, (X.1 p).store⟩,
              D.encrypt (G.stretch sa).1 m.1 (dec (enc (acdIDHdr X p) m.2))) := by
          simp [acdIDSM, acdIDBase, acdSMAD, acdIDJoin,
              SMSt.toScheme, ACDIDSt.withBase, hsnd, acdIDHdr]
        simp only [h1]
        cases ideal
        · simp only [challCt, Bool.false_eq_true, ite_false, PMF.pure_bind]
          refine congrArg PMF.pure (Prod.ext rfl (SMSchemeSt.ext_of ?_ rfl rfl rfl))
          funext q
          by_cases hq : q = p
          · subst hq
            simp [acdIDXUpd, acdIDJoin, SMSchemeSt.upd, SMLoc.advanced,
              SMSt.toScheme, ACDIDSt.withBase]
          · simp [acdIDXUpd, acdIDJoin, SMSchemeSt.upd, SMLoc.advanced,
              SMSt.toScheme, ACDIDSt.withBase,
              Function.update_of_ne hq]
        · simp only [challCt, ite_true, acdIDSM, acdIDBase, acdSMAD]
          refine congrArg _ (funext fun c => ?_)
          refine congrArg PMF.pure (Prod.ext rfl (SMSchemeSt.ext_of ?_ rfl rfl rfl))
          funext q
          by_cases hq : q = p
          · subst hq
            simp [acdIDXUpd, acdIDJoin, SMSchemeSt.upd, SMLoc.advanced,
              SMSt.toScheme, ACDIDSt.withBase]
          · simp [acdIDXUpd, acdIDJoin, SMSchemeSt.upd, SMLoc.advanced,
              SMSt.toScheme, ACDIDSt.withBase,
              Function.update_of_ne hq]
      · simp only [hc, Bool.false_eq_true, ite_false, PMF.pure_map]
        rfl
  | corrupt p =>
    have hcor : ckaAllowCorr ΔFS ΔPCS t (acdIDJoin σ X).ck p = ckaAllowCorr ΔFS ΔPCS t σ.ck p :=
      rfl
    simp only [smSchemeOracle, smOracleOf, SMQuery.mapMsg, PMF.pure_map, hcor]
    cases ckaAllowCorr ΔFS ΔPCS t σ.ck p
    · rfl
    · rfl

end Join

/-! ## Deliveries beside the base -/

section Deliver

variable {Sc Msg Key Rand RK Sa W Ct : Type} [SampleableType W] [SampleableType Ct]
  [DecidableEq Msg] [DecidableEq W] [DecidableEq Ct]

omit [SampleableType W] [SampleableType Ct] [DecidableEq W] [DecidableEq Ct] in
/-- The key lookup of `acdIDSM` reads the base state only through the receiving chain. -/
theorem acdIDRKey_base_congr (G : PRGDef Sa (W × Sa)) (maxSkip maxStored : ℕ)
    {Sc' RK' : Type} (x : ACDIDSt Sc' RK' Sa Msg W) (b : SMPartySt Sc RK Sa)
    (hb : b.rcv = x.base.rcv) (h : ACDHdr Msg) :
    acdIDRKey G maxSkip maxStored (x.withBase b) h =
      (acdIDRKey G maxSkip maxStored x h).map fun y => (y.1.withBase b, y.2) := by
  simp only [acdIDRKey, ACDIDSt.withBase, hb]
  split
  · rfl
  · split_ifs <;> simp [Option.map_map, Function.comp_def]

omit [SampleableType W] [SampleableType Ct] [DecidableEq Msg] [DecidableEq W] [DecidableEq Ct] in
/-- The state of party `p` with the receiving chain `rcv` in place of the one of its base
state. -/
def acdIDRcvSt (rcv : CKAParty → Option Sa) (X : CKAParty → ACDIDSt Unit Unit Sa Msg W)
    (p : CKAParty) : ACDIDSt Unit Unit Sa Msg W :=
  (X p).withBase ⟨(), (), none, rcv p⟩

/-- **The delivery of the game with decryption from the log beside the base**, with the
receiving chains `rcv` and the epoch counters `sh`: the answer from the log, the bookkeeping of
the parties and of the game after it, and the flag of a forgery at the epoch `k`. -/
def acdIDDeliver (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (maxSkip maxStored ΔFS ΔPCS k : ℕ) (rcv : CKAParty → Option Sa) (sh : CKAGameSt Unit Unit)
    (X : CKAParty → ACDIDSt Unit Unit Sa Msg W) (x : SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct)
    (p : CKAParty) (h : ACDHdr Msg) (ad : W) (c : Ct) :
    Option W × ((CKAParty → ACDIDSt Unit Unit Sa Msg W) × SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct) ×
      Bool :=
  match x.epochOf sh p h.1 with
  | none => (none, (X, x), false)
  | some e =>
    if x.safe ΔFS ΔPCS p e h.2 then
      match acdIDRKey G maxSkip maxStored (acdIDRcvSt rcv X p) h with
      | none => (none, (X, x), false)
      | some y =>
        ((x.findEntry e h ad c).map SMIDLogEntry.pt,
          (match x.findEntry e h ad c with
            | some _ => (Function.update X p y.1, x.mark e h ad c)
            | none => (X, x)),
          decide (e = k) && (D.decrypt y.2 c (ad, h) != (x.findEntry e h ad c).map SMIDLogEntry.pt))
    else (none, (X, x), false)

variable [Fintype Rand] [Nonempty Rand] [Fintype RK] [Nonempty RK] [Inhabited Msg]

omit [Fintype Rand] [Nonempty Rand] in
/-- **The delivery over `acdIDSM` beside the base.** The delivery with decryption from the log
at a joined state, and the forgery event at the epoch `k`, are those of `acdIDDeliver` at the
receiving chains and the epoch counters of the base. -/
theorem acdIDDeliver_join (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS k : ℕ)
    (σ : SMSt Sc Msg RK Sa) (X : ACDIDX Sa Msg W) (x : SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct)
    (p : CKAParty) (h : ACDHdr Msg) (ad : W) (c : Ct) :
    smIDDeliver (acdIDSM C R G D dec enc maxSkip maxStored) ΔFS ΔPCS (fun _ => true)
        (acdIDJoin σ X, x) p h ad c =
      ((acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k σ.loc.rcv (ckaShadow σ.ck) X.1 x p h ad c).1,
        (acdIDJoin σ ((acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k σ.loc.rcv (ckaShadow σ.ck)
          X.1 x p h ad c).2.1.1, X.2),
          (acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k σ.loc.rcv (ckaShadow σ.ck) X.1 x p h ad
            c).2.1.2)) ∧
    smIDBadAt (acdIDSM C R G D dec enc maxSkip maxStored) ΔFS ΔPCS k (acdIDJoin σ X, x)
        (.deliver p h ad c) =
      (acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k σ.loc.rcv (ckaShadow σ.ck) X.1 x p h ad
        c).2.2 := by
  have hst : (acdIDJoin σ X).ck.st p =
      (acdIDRcvSt σ.loc.rcv X.1 p).withBase (σ.toScheme.ck.st p) := rfl
  have hk : (acdIDSM C R G D dec enc maxSkip maxStored).rkey ((acdIDJoin σ X).ck.st p) h =
      (acdIDRKey G maxSkip maxStored (acdIDRcvSt σ.loc.rcv X.1 p) h).map
        fun y => (y.1.withBase (σ.toScheme.ck.st p), y.2) := by
    rw [hst]
    exact acdIDRKey_base_congr G maxSkip maxStored (acdIDRcvSt σ.loc.rcv X.1 p)
      (σ.toScheme.ck.st p) rfl h
  have hsh : ckaShadow (acdIDJoin σ X).ck = ckaShadow σ.ck := rfl
  simp only [smIDDeliver, smIDBadAt, acdIDDeliver, hk, hsh]
  have hpub : (acdIDSM C R G D dec enc maxSkip maxStored).hdrPub h = h.1 := rfl
  have hpos : (acdIDSM C R G D dec enc maxSkip maxStored).hdrPos h = h.2 := rfl
  simp only [hpub, hpos]
  cases he : x.epochOf (ckaShadow σ.ck) p h.1 with
  | none => exact ⟨rfl, rfl⟩
  | some e =>
    by_cases hsafe : x.safe ΔFS ΔPCS p e h.2 = true
    · simp only [hsafe, ite_true]
      cases hr : acdIDRKey G maxSkip maxStored (acdIDRcvSt σ.loc.rcv X.1 p) h with
      | none => exact ⟨rfl, by simp⟩
      | some y =>
        have hb : y.1.base = (acdIDRcvSt σ.loc.rcv X.1 p).base :=
          acdIDRKey_base G maxSkip maxStored _ h y hr
        cases hf : x.findEntry e h ad c with
        | none =>
          refine ⟨rfl, ?_⟩
          simp only [Bool.and_true, Option.map_some, Option.map_none]
          rfl
        | some l =>
          refine ⟨?_, ?_⟩
          rotate_left
          · simp only [Bool.and_true, Option.map_some]
            rfl
          simp only [Option.map_some, Prod.mk.injEq, true_and, and_true]
          refine SMSchemeSt.ext_of (funext fun q => ?_) rfl rfl rfl
          by_cases hq : q = p
          · subst hq
            simp [SMSchemeSt.upd, acdIDJoin]
          · simp [SMSchemeSt.upd, acdIDJoin, Function.update_of_ne hq]
    · simp [hsafe]

end Deliver

/-! ## The truncated forgery game beside the base -/

section Hop

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [Fintype RK] [Nonempty RK] [Inhabited Msg] [DecidableEq Msg]
  [DecidableEq W] [DecidableEq Ct]

/-- The states of the hop games: the state of the secure-messaging game of the base, the
bookkeeping of `acdIDSM` beside it, the bookkeeping of the game with immediate decryption and
the flag of a forgery. -/
abbrev ACDIDHopSt (Sc Msg RK Sa W Ct : Type) :=
  ((SMSt Sc Msg RK Sa × ACDIDX Sa Msg W) × SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct) × Bool

/-- The answers of the game with immediate decryption over `acdIDSM`. -/
abbrev ACDIDAns (Sc Msg RK Sa W Ct : Type) :=
  SMIDAns (Msg × ℕ) (ACDHdr Msg) Ct (ACDIDLeak Sc RK Sa Msg W) W

/-- The initial bookkeeping beside the initial state `σ` of the base. -/
def acdIDXInit : ACDIDX Sa Msg W :=
  (fun _ => ACDIDSt.embed ⟨(), (), none, none⟩, 0)

/-- The rejection of every transition into a state with the epoch `k` outside the safe
epochs. -/
def acdIDCut {S' Pub Hdr Leak : Type} (ΔFS ΔPCS k : ℕ)
    (x : SMIDAns Pub Hdr Ct Leak W × ((S' × SMIDAux W Pub Hdr Ct) × Bool)) :
    SMIDAns Pub Hdr Ct Leak W × ((S' × SMIDAux W Pub Hdr Ct) × Bool) :=
  if x.2.1.2.epochSafe ΔFS ΔPCS k = false then (.dec none, x.2) else x

/-- The flagged oracle of the game with decryption from the log over `acdIDSM`, on the states of
the secure-messaging game of the base with the root step `root` at the opening of the epoch `k`
and the challenge and corruption gates of the challenge epoch `t`. -/
noncomputable def acdIDHopStep (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS t k : ℕ)
    (root : RK → Key → PMF (RK × Sa)) (s : ACDIDHopSt Sc Msg RK Sa W Ct) :
    SMIDQuery W (ACDHdr Msg) Ct → PMF (ACDIDAns Sc Msg RK Sa W Ct × ACDIDHopSt Sc Msg RK Sa W Ct)
  | .sm q =>
    if smIDGate s.1.2 (ckaShadow s.1.1.1.ck) q then
      (smOracleOfAt C R G (aeadComapAD D dec) ΔFS ΔPCS t k false root s.1.1.1
        (q.mapMsg fun m => (m.1, enc (acdIDHdr s.1.1.2 q.party) m.2))).map fun y =>
        (.sm ((acdIDAns (s.1.1.2.1 q.party) y.1).withHdr (acdIDHdr s.1.1.2 q.party)),
          (((y.2, acdIDXUpd G s.1.1.1.loc.rcv (ckaShadow s.1.1.1.ck) s.1.1.1.ck.msg s.1.1.2 q y.1),
            s.1.2.upd Prod.snd (ckaShadow s.1.1.1.ck) q
              ((acdIDAns (s.1.1.2.1 q.party) y.1).withHdr (acdIDHdr s.1.1.2 q.party))), s.2))
    else PMF.pure (.sm .none, s)
  | .deliver p h ad c =>
    PMF.pure (.dec (acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k s.1.1.1.loc.rcv
        (ckaShadow s.1.1.1.ck) s.1.1.2.1 s.1.2 p h ad c).1,
      (((s.1.1.1, ((acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k s.1.1.1.loc.rcv
          (ckaShadow s.1.1.1.ck) s.1.1.2.1 s.1.2 p h ad c).2.1.1, s.1.1.2.2)),
        (acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k s.1.1.1.loc.rcv (ckaShadow s.1.1.1.ck)
          s.1.1.2.1 s.1.2 p h ad c).2.1.2),
        s.2 || (acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k s.1.1.1.loc.rcv
          (ckaShadow s.1.1.1.ck) s.1.1.2.1 s.1.2 p h ad c).2.2))

/-- **The truncated hybrid over `acdIDSM` with the root step `root` at the epoch `k`**:
`acdIDHopStep` until the first answered corruption with the epoch `k` in its window, which is
answered by a rejection, and a rejection of every later query. -/
noncomputable def acdIDHopOracle (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS t k : ℕ)
    (root : RK → Key → PMF (RK × Sa)) (s : ACDIDHopSt Sc Msg RK Sa W Ct)
    (d : SMIDQuery W (ACDHdr Msg) Ct) :
    PMF (ACDIDAns Sc Msg RK Sa W Ct × ACDIDHopSt Sc Msg RK Sa W Ct) :=
  (if s.1.2.epochSafe ΔFS ΔPCS k then
      acdIDHopStep C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k root s d
    else PMF.pure (.dec none, s)).map (acdIDCut ΔFS ΔPCS k)

/-- **The forgery game at the epoch `k` over `acdIDSM` with the root step `root` at the epoch
`k`**: the run of `A` against `acdIDHopOracle` from the initial state, with the flag of a
forgery as output. At the real root step it is the truncated forgery game with decryption from
the log (`acdIDSM_logTruncGame_eq_hop`). -/
noncomputable def acdIDHopGame (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS k : ℕ)
    (root : RK → Key → PMF (RK × Sa))
    (A : SMIDAdv (Msg × ℕ) W (ACDHdr Msg) Ct (ACDIDLeak Sc RK Sa Msg W)) : SPComp Bool :=
  SPComp.bind (liftPMF A.tStar) fun t => SPComp.bind C.init fun i =>
    SPComp.bind (SPComp.sample RK) fun rk =>
      liftPMF ((OracleAdv.run
        (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k root) (A.play t (i.1, 0))
        (((smInit i rk, acdIDXInit), SMIDAux.init (i.1, 0)), false)).map
          fun x => x.2.2)

/-- The state of the game with decryption from the log over `acdIDSM` that a state of the hop
games corresponds to. -/
def acdIDEmb (s : ACDIDHopSt Sc Msg RK Sa W Ct) :
    (SMSchemeSt (ACDIDSt Sc RK Sa Msg W) (Msg × ℕ) × SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct) ×
      Bool :=
  ((acdIDJoin s.1.1.1 s.1.1.2, s.1.2), s.2)

/-- **The hop oracle at the real root step is the truncated oracle over `acdIDSM`.** Under the
invariant `ACDInv`, each call of `acdIDHopOracle` at the real root step, carried to the states
of the game over `acdIDSM`, is the call of `smIDTruncOracle` with decryption from the log, with
the transitions into a corruption of the epoch `k` answered by a rejection. -/
theorem acdIDHop_step (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored : ℕ)
    (J : Sc → Sc → Prop) (ΔFS ΔPCS t k : ℕ) (s : ACDIDHopSt Sc Msg RK Sa W Ct)
    (hs : ACDInv C R J s.1.1.1) (d : SMIDQuery W (ACDHdr Msg) Ct) :
    (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k (realRoot R) s d).map
        (Prod.map id acdIDEmb) =
      (smIDTruncOracle (acdIDSM C R G D dec enc maxSkip maxStored) ΔFS ΔPCS t false
        (fun _ => true) k (acdIDEmb s) d).map (acdIDCut ΔFS ΔPCS k) := by
  obtain ⟨⟨⟨σ, X⟩, x⟩, b⟩ := s
  have hc : (Prod.map id acdIDEmb ∘ acdIDCut ΔFS ΔPCS k) =
      (acdIDCut ΔFS ΔPCS k ∘ Prod.map id acdIDEmb :
        ACDIDAns Sc Msg RK Sa W Ct × ACDIDHopSt Sc Msg RK Sa W Ct → _) := by
    funext y
    obtain ⟨a, ⟨⟨⟨σ', X'⟩, x'⟩, b'⟩⟩ := y
    by_cases h : x'.epochSafe ΔFS ΔPCS k = false <;> simp [acdIDCut, acdIDEmb, h]
  rw [acdIDHopOracle, PMF.map_comp, hc, ← PMF.map_comp]
  congr 1
  simp only [smIDTruncOracle, acdIDEmb]
  by_cases hx : x.epochSafe ΔFS ΔPCS k = true
  · simp only [hx, ite_true]
    cases d with
    | sm q =>
      simp only [acdIDHopStep, smIDFlagOracle, smIDOracleAt, smIDBadAt, Bool.or_false]
      have hg : smIDGate x (ckaShadow (acdIDJoin σ X).ck) q = smIDGate x (ckaShadow σ.ck) q :=
        rfl
      rw [hg]
      split_ifs with hgate
      · rw [smOracleOfAt_realRoot, acdIDSM_scheme_step C R G D dec enc maxSkip maxStored J ΔFS
          ΔPCS t false σ X hs q, PMF.map_comp, PMF.map_comp, PMF.map_comp]
        rfl
      · simp only [PMF.pure_map]
        rfl
    | deliver p h ad c =>
      obtain ⟨h1, h2⟩ := acdIDDeliver_join C R G D dec enc maxSkip maxStored ΔFS ΔPCS k σ X x p
        h ad c
      simp only [acdIDHopStep, smIDFlagOracle, smIDOracleAt, PMF.pure_map, h1, h2]
      rfl
  · simp only [hx, Bool.false_eq_true, ite_false, PMF.pure_map]
    rfl

omit [Fintype RK] [Nonempty RK] [Inhabited Msg] in
/-- The hop oracle at the real root step keeps the invariant `ACDInv`, when the CKA is correct
along `J`. -/
theorem acdIDHop_acdInv (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored : ℕ)
    {J : Sc → Sc → Prop} (hJ : CKACorrect C J) (ΔFS ΔPCS t k : ℕ)
    (s : ACDIDHopSt Sc Msg RK Sa W Ct) (hs : ACDInv C R J s.1.1.1)
    (d : SMIDQuery W (ACDHdr Msg) Ct) :
    ∀ y ∈ (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k (realRoot R) s d).support,
      ACDInv C R J y.2.1.1.1 := by
  intro y hy
  simp only [acdIDHopOracle, PMF.support_map, Set.mem_image] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  have hz2 : (acdIDCut ΔFS ΔPCS k z).2 = z.2 := by
    unfold acdIDCut
    split <;> rfl
  rw [hz2]
  split at hz
  · cases d with
    | sm q =>
      simp only [acdIDHopStep] at hz
      split at hz
      · simp only [PMF.support_map, Set.mem_image] at hz
        obtain ⟨w, hw, rfl⟩ := hz
        rw [smOracleOfAt_realRoot] at hw
        exact acdInv_step C R G (aeadComapAD D dec) hJ ΔFS ΔPCS t false _ hs _ w hw
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact hs
    | deliver p h ad c =>
      simp only [acdIDHopStep, PMF.support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hs
  · simp only [PMF.support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hs

/-- **The truncated forgery game over `acdIDSM` with decryption from the log is the hop game at
the real root step.** For a CKA correct along `J`, with an initialisation that is the lift of
`initP` and initial states related by `J`. -/
theorem acdIDSM_logTruncGame_eq_hop (C : CKADef Sc Msg Key) [CKACoins C Rand]
    {J : Sc → Sc → Prop} (hJ : CKACorrect C J) (initP : PMF (Msg × Sc × Sc))
    (hinit : C.init = liftPMF initP) (hJi : ∀ i ∈ initP.support, J i.2.1 i.2.2)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS k : ℕ)
    (A : SMIDAdv (Msg × ℕ) W (ACDHdr Msg) Ct (ACDIDLeak Sc RK Sa Msg W)) :
    smIDLogTruncGame (acdIDSM C R G D dec enc maxSkip maxStored) ΔFS ΔPCS k A =
      acdIDHopGame C R G D dec enc maxSkip maxStored ΔFS ΔPCS k (realRoot R) A := by
  have hI : (acdIDSM C R G D dec enc maxSkip maxStored).init =
      SPComp.bind C.init fun i => SPComp.bind (SPComp.sample RK) fun rk =>
        SPComp.pure ((i.1, 0), (ACDIDSt.embed ⟨i.2.1, rk, none, none⟩ : ACDIDSt Sc RK Sa Msg W),
          (ACDIDSt.embed ⟨i.2.2, rk, none, none⟩ : ACDIDSt Sc RK Sa Msg W)) := by
    simp only [acdIDSM, acdIDBase, acdSMAD, SPComp.bind_assoc, SPComp.pure_bind]
  simp only [smIDLogTruncGame, acdIDHopGame, hI, hinit, sample_eq_liftPMF, SPComp.bind_assoc,
    SPComp.pure_bind, liftPMF_bind_liftPMF]
  refine congrArg _ (congrArg _ (funext fun t => ?_))
  refine PMF.bind_congr_support _ _ _ fun i hi => congrArg _ (funext fun rk => ?_)
  have hfr : ∀ (s : (SMSchemeSt (ACDIDSt Sc RK Sa Msg W) (Msg × ℕ) ×
      SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct) × Bool) d,
      s.1.2.epochSafe ΔFS ΔPCS k = false → ∀ x ∈ (smIDTruncOracle
        (acdIDSM C R G D dec enc maxSkip maxStored) ΔFS ΔPCS t false (fun _ => true) k
          s d).support, x.2.1.2.epochSafe ΔFS ΔPCS k = false ∧ x.2.2 = s.2 := by
    intro s d hs x hx
    simp only [smIDTruncOracle, hs, Bool.false_eq_true, ite_false, PMF.support_pure,
      Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨hs, rfl⟩
  refine Eq.trans (OracleAdv.run_map_eq_of_cut _
    (fun s : (SMSchemeSt (ACDIDSt Sc RK Sa Msg W) (Msg × ℕ) ×
      SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct) × Bool => s.1.2.epochSafe ΔFS ΔPCS k = false)
    (fun s => s.2) (SMIDAns.dec none) hfr _ _).symm ?_
  have he : acdIDEmb (((smInit i rk, acdIDXInit),
      (SMIDAux.init (i.1, 0) : SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct)), false) =
      ((SMSchemeSt.init ((i.1, 0), (ACDIDSt.embed ⟨i.2.1, rk, none, none⟩ : ACDIDSt Sc RK Sa Msg W),
        (ACDIDSt.embed ⟨i.2.2, rk, none, none⟩ : ACDIDSt Sc RK Sa Msg W)),
        SMIDAux.init (i.1, 0)), false) := by
    simp only [acdIDEmb, Prod.mk.injEq, and_true]
    refine SMSchemeSt.ext_of (funext fun q => ?_) rfl rfl rfl
    cases q <;> rfl
  rw [← he]
  have h := OracleAdv.run_map_state_of_inv _
    (fun s d => (smIDTruncOracle (acdIDSM C R G D dec enc maxSkip maxStored) ΔFS ΔPCS t false
      (fun _ => true) k s d).map (acdIDCut ΔFS ΔPCS k))
    acdIDEmb (fun s => ACDInv C R J s.1.1.1)
    (fun s d hs => acdIDHop_acdInv C R G D dec enc maxSkip maxStored hJ ΔFS ΔPCS t k s hs d)
    (fun s d hs => acdIDHop_step C R G D dec enc maxSkip maxStored J ΔFS ΔPCS t k s hs d)
    (A.play t (i.1, 0)) (((smInit i rk, acdIDXInit), SMIDAux.init (i.1, 0)), false)
    (acdInv_smInit C R i (hJi i hi) rk)
  refine Eq.trans (congrArg (PMF.map fun x => x.2.2) h.symm) ?_
  rw [PMF.map_comp]
  rfl

/-- The CKA message in transit after the query `q` with the answer `a` of the game over the
base: the message of an opened epoch, or the message `T₀` before. -/
def acdIDMsgUpd {Sc RK Sa Ct' : Type} (T₀ : Msg) : SMQuery W → SMAns Sc Msg RK Sa Ct' → Msg
  | .ratchet _, .msg T => T
  | _, _ => T₀

omit [Fintype RK] [Nonempty RK] [Inhabited Msg] [DecidableEq Msg] [DecidableEq W]
  [DecidableEq Ct] in
/-- The CKA message in transit after a call of `smOracleOfAt`. -/
theorem smOracleOfAt_msg (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t k : ℕ) (ideal : Bool) (root : RK → Key → PMF (RK × Sa))
    (s : SMSt Sc Msg RK Sa) (q : SMQuery W) :
    ∀ y ∈ (smOracleOfAt C R G D ΔFS ΔPCS t k ideal root s q).support,
      y.2.ck.msg = acdIDMsgUpd s.ck.msg q y.1 := by
  intro y hy
  cases q with
  | ratchet p =>
    simp only [smOracleOfAt, smOracleOf] at hy
    split at hy
    · simp only [PMF.support_bind, Set.mem_iUnion, PMF.support_pure, Set.mem_singleton_iff]
        at hy
      obtain ⟨r, -, z, -, rfl⟩ := hy
      rfl
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
      subst hy
      rfl
  | recv p =>
    simp only [smOracleOfAt, smOracleOf] at hy
    split at hy <;> simp only [PMF.support_pure, Set.mem_singleton_iff] at hy <;> subst hy <;> rfl
  | send p m =>
    simp only [smOracleOfAt, smOracleOf] at hy
    split at hy
    · split at hy <;> simp only [PMF.support_pure, Set.mem_singleton_iff] at hy <;> subst hy <;>
        rfl
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
      subst hy
      rfl
  | chall p m =>
    simp only [smOracleOfAt, smOracleOf] at hy
    split at hy
    · split at hy
      · simp only [PMF.support_bind, Set.mem_iUnion, PMF.support_pure, Set.mem_singleton_iff]
          at hy
        obtain ⟨c, -, rfl⟩ := hy
        rfl
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
        subst hy
        rfl
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
      subst hy
      rfl
  | corrupt p =>
    simp only [smOracleOfAt, smOracleOf, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    rfl

omit [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct] [Fintype RK]
  [Nonempty RK] [Inhabited Msg] [DecidableEq Msg] [DecidableEq W] [DecidableEq Ct] in
/-- The epoch `k` stays among the safe epochs after a query that is not an answered corruption
with the epoch `k` in its window. -/
theorem SMIDAux.epochSafe_upd_of_true {Pub Hdr Leak : Type} (ΔFS ΔPCS k : ℕ) (pos : Hdr → ℕ)
    (x : SMIDAux W Pub Hdr Ct) (sh : CKAGameSt Unit Unit) (q : SMQuery W)
    (a : SMSchemeAns Pub (Hdr × Ct) Leak) (h : x.epochSafe ΔFS ΔPCS k = true)
    (hq : ∀ p l, q = .corrupt p → a = .state l → ckaAllowCorr ΔFS ΔPCS k sh p = true) :
    (x.upd pos sh q a).epochSafe ΔFS ΔPCS k = true := by
  cases q <;> cases a <;> try exact h
  rename_i p l
  simp only [SMIDAux.upd, SMIDAux.epochSafe, List.all_cons, Bool.and_eq_true]
  exact ⟨hq p l rfl rfl, h⟩

end Hop

/-! ## The CKA hop -/

section CKAHop

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [Fintype RK] [Nonempty RK] [Inhabited Msg] [DecidableEq Msg]
  [DecidableEq W] [DecidableEq Ct]

/-- The states of the simulator of the CKA hop: the part `SMLoc` of the secure-messaging state,
the epoch counters, the bookkeeping of `acdIDSM` beside the base with the CKA message in transit,
the bookkeeping of the game with immediate decryption and the flag of a forgery. -/
abbrev ACDIDCKASt (Msg RK Sa W Ct : Type) :=
  (((SMLoc RK Sa × CKAGameSt Unit Unit) × (ACDIDX Sa Msg W × Msg)) ×
    SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct) × Bool

/-- A query of the corruption game forwarded to `smCKAImplAt` and completed as in
`acdIDHopStep`. -/
noncomputable def acdIDCKAFwd (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct (W × ACDHdr Msg)) (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W)
    (ΔFS ΔPCS t k : ℕ) (σ : ACDIDCKASt Msg RK Sa W Ct) (q : SMQuery W) :
    OracleAdv CKAQuery (CKAAns Sc Msg Key Rand)
      (ACDIDAns Sc Msg RK Sa W Ct × ACDIDCKASt Msg RK Sa W Ct) :=
  (smCKAImplAt R G (aeadComapAD D dec) ΔFS ΔPCS t k false σ.1.1.1
    (q.mapMsg fun m => (m.1, enc (acdIDHdr σ.1.1.2.1 q.party) m.2))).bind fun r =>
    .ret (.sm ((acdIDAns (σ.1.1.2.1.1 q.party) r.1).withHdr (acdIDHdr σ.1.1.2.1 q.party)),
      (((r.2, (acdIDXUpd G σ.1.1.1.1.rcv σ.1.1.1.2 σ.1.1.2.2 σ.1.1.2.1 q r.1,
          acdIDMsgUpd σ.1.1.2.2 q r.1)),
        σ.1.2.upd Prod.snd σ.1.1.1.2 q
          ((acdIDAns (σ.1.1.2.1.1 q.party) r.1).withHdr (acdIDHdr σ.1.1.2.1 q.party))), σ.2))

/-- **The simulator of the CKA reduction of the forgery event at the epoch `k`**: queries of the
corruption game that pass the gate are forwarded by `acdIDCKAFwd`, deliveries are answered by
`acdIDDeliver` from the receiving chains of the simulator, and a corruption with the epoch `k` in
its window stops the simulation. -/
noncomputable def acdIDCKAImpl (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct (W × ACDHdr Msg)) (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W)
    (maxSkip maxStored ΔFS ΔPCS t k : ℕ) (σ : ACDIDCKASt Msg RK Sa W Ct)
    (d : SMIDQuery W (ACDHdr Msg) Ct) :
    OracleAdv CKAQuery (CKAAns Sc Msg Key Rand)
      (ACDIDAns Sc Msg RK Sa W Ct × ACDIDCKASt Msg RK Sa W Ct) :=
  if σ.1.2.epochSafe ΔFS ΔPCS k then
    match d with
    | .sm q =>
      if smIDGate σ.1.2 σ.1.1.1.2 q then
        match q with
        | .ratchet p => acdIDCKAFwd R G D dec enc ΔFS ΔPCS t k σ (.ratchet p)
        | .recv p => acdIDCKAFwd R G D dec enc ΔFS ΔPCS t k σ (.recv p)
        | .send p m => acdIDCKAFwd R G D dec enc ΔFS ΔPCS t k σ (.send p m)
        | .chall p m => acdIDCKAFwd R G D dec enc ΔFS ΔPCS t k σ (.chall p m)
        | .corrupt p =>
          if ckaAllowCorr ΔFS ΔPCS t σ.1.1.1.2 p && !ckaAllowCorr ΔFS ΔPCS k σ.1.1.1.2 p then
            .ret (.dec none, ((σ.1.1, { σ.1.2 with
              corrs := (p, σ.1.1.1.2, σ.1.2.pending σ.1.1.1.2 p) :: σ.1.2.corrs }), σ.2))
          else acdIDCKAFwd R G D dec enc ΔFS ΔPCS t k σ (.corrupt p)
      else .ret (.sm .none, σ)
    | .deliver p h ad c =>
      .ret (.dec (acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k σ.1.1.1.1.rcv σ.1.1.1.2
          σ.1.1.2.1.1 σ.1.2 p h ad c).1,
        (((σ.1.1.1, (((acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k σ.1.1.1.1.rcv σ.1.1.1.2
            σ.1.1.2.1.1 σ.1.2 p h ad c).2.1.1, σ.1.1.2.1.2), σ.1.1.2.2)),
          (acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k σ.1.1.1.1.rcv σ.1.1.1.2 σ.1.1.2.1.1 σ.1.2
            p h ad c).2.1.2),
          σ.2 || (acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k σ.1.1.1.1.rcv σ.1.1.1.2
            σ.1.1.2.1.1 σ.1.2 p h ad c).2.2))
  else .ret (.dec none, σ)

/-- The CKA reduction of the forgery event at the epoch `k` as an oracle tree: on the CKA
challenge epoch `k` and the public value `pub`, it draws the challenge epoch `t` of the adversary
from `tStar` and a uniform root key, runs the adversary against `acdIDCKAImpl` and outputs the
flag of a forgery. -/
noncomputable def acdIDCKATree (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct (W × ACDHdr Msg)) (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W)
    (maxSkip maxStored ΔFS ΔPCS : ℕ) (tStar : PMF ℕ)
    (play : ℕ → Msg × ℕ → OracleAdv (SMIDQuery W (ACDHdr Msg) Ct) (ACDIDAns Sc Msg RK Sa W Ct)
      Bool) (k : ℕ) (pub : Msg) : OracleAdv CKAQuery (CKAAns Sc Msg Key Rand) Bool :=
  .rand tStar fun t => .rand (PMF.uniformFintype RK) fun rk =>
    (OracleAdv.simulate (acdIDCKAImpl R G D dec enc maxSkip maxStored ΔFS ΔPCS t k)
      (play t (pub, 0)) ((((SMLoc.init rk, CKAGameSt.init () () ()), (acdIDXInit, pub)),
        SMIDAux.init (pub, 0)), false)).bind fun r => .ret r.2.2

/-- **The CKA reduction of the forgery event at the epoch `k`** over `acdIDSM`: the CKA adversary
with the challenge epoch `k` that plays the tree `acdIDCKATree`. -/
noncomputable def acdIDCKARed (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct (W × ACDHdr Msg)) (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W)
    (maxSkip maxStored ΔFS ΔPCS k : ℕ)
    (A : SMIDAdv (Msg × ℕ) W (ACDHdr Msg) Ct (ACDIDLeak Sc RK Sa Msg W)) :
    CKACorruptAdv Sc Msg Key Rand Bool where
  tStar := PMF.pure k
  play := acdIDCKATree R G D dec enc maxSkip maxStored ΔFS ΔPCS A.tStar A.play

/-- The state of the CKA reduction and of the CKA game that a state of the hop games
corresponds to. -/
def acdIDCKAEmb (s : ACDIDHopSt Sc Msg RK Sa W Ct) :
    ACDIDCKASt Msg RK Sa W Ct × CKAGameSt Sc Msg :=
  (((((s.1.1.1.loc, ckaShadow s.1.1.1.ck), (s.1.1.2, s.1.1.1.ck.msg)), s.1.2), s.2), s.1.1.1.ck)

omit [Fintype Rand] [Nonempty Rand] [SampleableType Ct] [Fintype RK] [Nonempty RK]
  [Inhabited Msg] in
/-- A delivery keeps the answered corruptions. -/
theorem acdIDDeliver_epochSafe (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (maxSkip maxStored ΔFS ΔPCS k k' : ℕ) (rcv : CKAParty → Option Sa) (sh : CKAGameSt Unit Unit)
    (X : CKAParty → ACDIDSt Unit Unit Sa Msg W) (x : SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct)
    (p : CKAParty) (h : ACDHdr Msg) (ad : W) (c : Ct) :
    (acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k rcv sh X x p h ad c).2.1.2.epochSafe ΔFS ΔPCS
      k' = x.epochSafe ΔFS ΔPCS k' := by
  unfold acdIDDeliver
  split
  · rfl
  · split_ifs
    · split
      · rfl
      · split <;> rfl
    · rfl

omit [SampleableType W] [Inhabited Msg] [DecidableEq Msg] [DecidableEq W] [DecidableEq Ct]
  [Fintype RK] [Nonempty RK] in
/-- The CKA message after a query with relabelled messages. -/
theorem acdIDMsgUpd_mapMsg {Sc RK Sa Ct' : Type} (T₀ : Msg) (f : W × W → W × W) (q : SMQuery W)
    (a : SMAns Sc Msg RK Sa Ct') : acdIDMsgUpd T₀ (q.mapMsg f) a = acdIDMsgUpd T₀ q a := by
  cases q <;> rfl

variable [Fintype Key] [Nonempty Key]

omit [Fintype RK] [Nonempty RK] [Inhabited Msg] in
/-- A forwarded query of the hop oracle with the root step `ckaHopRoot R idealK` at the epoch
`k`, from a state with the epoch `k` safe, through the gate and other than a corruption with the
epoch `k` in its window, is the forwarding simulator `acdIDCKAFwd` against the CKA oracle. -/
theorem acdIDHop_fwd (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS t k : ℕ)
    (idealK : Bool) (σ : SMSt Sc Msg RK Sa) (X : ACDIDX Sa Msg W)
    (x : SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct) (b : Bool) (q : SMQuery W)
    (hx : x.epochSafe ΔFS ΔPCS k = true) (hg : smIDGate x (ckaShadow σ.ck) q = true)
    (hq : ∀ p, q = .corrupt p → ckaAllowCorr ΔFS ΔPCS t σ.ck p = true →
      ckaAllowCorr ΔFS ΔPCS k σ.ck p = true) :
    (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k (ckaHopRoot R idealK)
        (((σ, X), x), b) (.sm q)).map (Prod.map id acdIDCKAEmb) =
      OracleAdv.simOracle (acdIDCKAFwd R G D dec enc ΔFS ΔPCS t k)
        (ckaOracleP C ΔFS ΔPCS k idealK) (acdIDCKAEmb (((σ, X), x), b)) q := by
  have hq' : ∀ p, q.mapMsg (fun m => (m.1, enc (acdIDHdr X q.party) m.2)) = .corrupt p →
      ckaAllowCorr ΔFS ΔPCS t σ.ck p = true → ckaAllowCorr ΔFS ΔPCS k σ.ck p = true := by
    intro p h1 h2
    cases q with
    | corrupt p' =>
      simp only [SMQuery.mapMsg, SMQuery.corrupt.injEq] at h1
      subst h1
      exact hq _ rfl h2
    | _ => simp [SMQuery.mapMsg] at h1
  have hsafe : ∀ y ∈ (smOracleOfAt C R G (aeadComapAD D dec) ΔFS ΔPCS t k false
      (ckaHopRoot R idealK) σ (q.mapMsg fun m => (m.1, enc (acdIDHdr X q.party) m.2))).support,
      (x.upd Prod.snd (ckaShadow σ.ck) q
        ((acdIDAns (X.1 q.party) y.1).withHdr (acdIDHdr X q.party))).epochSafe ΔFS ΔPCS k =
        true := by
    intro y hy
    refine SMIDAux.epochSafe_upd_of_true ΔFS ΔPCS k _ x _ q _ hx fun p l hqp hl => ?_
    subst hqp
    simp only [SMQuery.mapMsg, smOracleOfAt, smOracleOf, PMF.support_pure,
      Set.mem_singleton_iff] at hy
    subst hy
    by_cases h : ckaAllowCorr ΔFS ΔPCS t σ.ck p = true
    · exact hq p rfl h
    · simp [h, acdIDAns, SMSchemeAns.withHdr] at hl
  have hR : OracleAdv.simOracle (acdIDCKAFwd R G D dec enc ΔFS ΔPCS t k)
      (ckaOracleP C ΔFS ΔPCS k idealK) (acdIDCKAEmb (((σ, X), x), b)) q =
      (OracleAdv.simOracle (smCKAImplAt R G (aeadComapAD D dec) ΔFS ΔPCS t k false)
        (ckaOracleP C ΔFS ΔPCS k idealK) (smCKAEmb σ)
        (q.mapMsg fun m => (m.1, enc (acdIDHdr X q.party) m.2))).map fun z =>
          (SMIDAns.sm ((acdIDAns (X.1 q.party) z.1).withHdr (acdIDHdr X q.party)),
            ((((z.2.1, (acdIDXUpd G σ.loc.rcv (ckaShadow σ.ck) σ.ck.msg X q z.1,
                acdIDMsgUpd σ.ck.msg q z.1)),
              x.upd Prod.snd (ckaShadow σ.ck) q
                ((acdIDAns (X.1 q.party) z.1).withHdr (acdIDHdr X q.party))), b), z.2.2)) := by
    simp only [OracleAdv.simOracle, acdIDCKAFwd, acdIDCKAEmb, smCKAEmb, OracleAdv.run_bind,
      OracleAdv.run_ret, PMF.map]
    simp only [PMF.bind_bind, PMF.pure_bind, Function.comp_apply]
  rw [hR, ← smCKAImplAt_step C R G (aeadComapAD D dec) ΔFS ΔPCS t k false idealK σ _ hq',
    PMF.map_comp, acdIDHopOracle, ite_eq_left_of_eq_true _ _ (eq_true hx), acdIDHopStep,
    ite_eq_left_of_eq_true _ _ (eq_true hg), PMF.map_comp, PMF.map_comp]
  simp only [PMF.map]
  refine PMF.bind_congr_support _ _ _ fun y hy => ?_
  have hm := smOracleOfAt_msg C R G (aeadComapAD D dec) ΔFS ΔPCS t k false _ σ _ y hy
  rw [acdIDMsgUpd_mapMsg] at hm
  simp only [Function.comp_apply, acdIDCut, hsafe y hy, Bool.true_eq_false, ite_false,
    Prod.map, id_eq, acdIDCKAEmb, smCKAEmb, hm]

omit [Fintype RK] [Nonempty RK] [Inhabited Msg] in
/-- **The CKA simulator of the forgery event is the hop oracle.** Each call of the hop oracle
with the root step `ckaHopRoot R idealK` at the epoch `k`, mapped to the states of the reduction
and of the CKA game, is the call of `acdIDCKAImpl` against the CKA oracle with the challenge
epoch `k` and the challenge mode `idealK`. -/
theorem acdIDHop_cka_step (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS t k : ℕ)
    (idealK : Bool) (s : ACDIDHopSt Sc Msg RK Sa W Ct) (d : SMIDQuery W (ACDHdr Msg) Ct) :
    (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k (ckaHopRoot R idealK) s d).map
        (Prod.map id acdIDCKAEmb) =
      OracleAdv.simOracle (acdIDCKAImpl R G D dec enc maxSkip maxStored ΔFS ΔPCS t k)
        (ckaOracleP C ΔFS ΔPCS k idealK) (acdIDCKAEmb s) d := by
  obtain ⟨⟨⟨σ, X⟩, x⟩, b⟩ := s
  have hsh : ∀ e p, ckaAllowCorr ΔFS ΔPCS e (ckaShadow σ.ck) p = ckaAllowCorr ΔFS ΔPCS e σ.ck p :=
    fun _ _ => rfl
  by_cases hx : x.epochSafe ΔFS ΔPCS k = true
  · cases d with
    | sm q =>
      by_cases hg : smIDGate x (ckaShadow σ.ck) q = true
      · cases q with
        | ratchet p =>
          rw [acdIDHop_fwd C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k idealK σ X x b _ hx hg
            (by simp)]
          simp only [OracleAdv.simOracle, acdIDCKAImpl, acdIDCKAEmb, hx, hg, ite_true]
        | recv p =>
          rw [acdIDHop_fwd C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k idealK σ X x b _ hx hg
            (by simp)]
          simp only [OracleAdv.simOracle, acdIDCKAImpl, acdIDCKAEmb, hx, hg, ite_true]
        | send p m =>
          rw [acdIDHop_fwd C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k idealK σ X x b _ hx hg
            (by simp)]
          simp only [OracleAdv.simOracle, acdIDCKAImpl, acdIDCKAEmb, hx, hg, ite_true]
        | chall p m =>
          rw [acdIDHop_fwd C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k idealK σ X x b _ hx hg
            (by simp)]
          simp only [OracleAdv.simOracle, acdIDCKAImpl, acdIDCKAEmb, hx, hg, ite_true]
        | corrupt p =>
          by_cases hs : ckaAllowCorr ΔFS ΔPCS t σ.ck p = true ∧
              ckaAllowCorr ΔFS ΔPCS k σ.ck p = false
          · have hx' : (x.corrs.all fun c => ckaAllowCorr ΔFS ΔPCS k c.2.1 c.1) = true := hx
            simp [acdIDHopOracle, acdIDHopStep, smOracleOfAt, smOracleOf, acdIDCut, acdIDCKAImpl,
              acdIDCKAEmb, OracleAdv.simOracle, hx', hg, hs, hsh, acdIDAns, SMSchemeAns.withHdr,
              SMIDAux.upd, SMIDAux.epochSafe, PMF.pure_map, acdIDXUpd, SMQuery.mapMsg,
              List.all_cons]
          · rw [acdIDHop_fwd C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k idealK σ X x b _ hx hg
              (fun p' h h1 => by cases h; grind)]
            simp only [not_and, Bool.not_eq_false] at hs
            simp [OracleAdv.simOracle, acdIDCKAImpl, acdIDCKAEmb, hx, hg, hsh]
            grind
      · simp [acdIDHopOracle, acdIDHopStep, acdIDCut, acdIDCKAImpl, acdIDCKAEmb,
          OracleAdv.simOracle, hx, hg, PMF.pure_map]
    | deliver p h ad c =>
      have he := acdIDDeliver_epochSafe G D maxSkip maxStored ΔFS ΔPCS k k σ.loc.rcv
        (ckaShadow σ.ck) X.1 x p h ad c
      simp only [acdIDHopOracle, acdIDHopStep, hx, ite_true, PMF.pure_map, acdIDCut, he,
        Bool.true_eq_false, ite_false, acdIDCKAImpl, OracleAdv.simOracle, OracleAdv.run_ret,
        acdIDCKAEmb]
      rfl
  · simp [acdIDHopOracle, acdIDCut, acdIDCKAImpl, acdIDCKAEmb, OracleAdv.simOracle, hx,
      PMF.pure_map]

/-- **The CKA hop of the forgery event over `acdIDSM`.** The CKA game with challenge mode
`idealK` of the reduction `acdIDCKARed` at the epoch `k` is the hop game with the root step
`ckaHopRoot R idealK` at the epoch `k`. -/
theorem acdIDHopGame_eq_cka (C : CKADef Sc Msg Key) [CKACoins C Rand] (hS : CKACoins.Sound C)
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS k : ℕ)
    (idealK : Bool) (A : SMIDAdv (Msg × ℕ) W (ACDHdr Msg) Ct (ACDIDLeak Sc RK Sa Msg W)) :
    cka_corrupt_game C ΔFS ΔPCS idealK
        (acdIDCKARed R G D dec enc maxSkip maxStored ΔFS ΔPCS k A) =
      acdIDHopGame C R G D dec enc maxSkip maxStored ΔFS ΔPCS k (ckaHopRoot R idealK) A := by
  rw [cka_corrupt_game_eq_liftPMF C hS initP hinit]
  simp only [acdIDHopGame, hinit, sample_eq_liftPMF, liftPMF_bind_liftPMF]
  congr 1
  simp only [acdIDCKARed, PMF.pure_bind, acdIDCKATree, OracleAdv.run_rand, PMF.map_bind]
  rw [PMF.bind_comm]
  refine congrArg _ (funext fun t => congrArg _ (funext fun i =>
    congrArg _ (funext fun rk => ?_)))
  rw [OracleAdv.run_bind, OracleAdv.run_simulate]
  have he : acdIDCKAEmb (((smInit (Sa := Sa) i rk, (acdIDXInit : ACDIDX Sa Msg W)),
      (SMIDAux.init (i.1, 0) : SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct)), false) =
      (((((SMLoc.init rk, CKAGameSt.init () () ()), (acdIDXInit, i.1)), SMIDAux.init (i.1, 0)),
        false), CKAGameSt.init i.1 i.2.1 i.2.2) := by
    simp only [acdIDCKAEmb, smInit, ckaShadow_init]
    rfl
  rw [← he, ← OracleAdv.run_map_state _ _ acdIDCKAEmb
    (acdIDHop_cka_step C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k idealK)]
  simp [PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def, PMF.pure_map]
  rfl

/-- **The CKA hop of the forgery event at the epoch `k` over `acdIDSM`.** For a CKA correct along
`J` with a sound explicit-randomness sending algorithm, an initialisation that is the lift of
`initP` and initial states related by `J`, the probability of a forgery at the epoch `k` in the
truncated game with decryption from the log is at most the CKA corruption advantage of
`acdIDCKARed … k A` plus the probability of a forgery in the hop game whose root step at the
epoch `k` takes a uniform key in place of the CKA key. -/
theorem acdIDSM_logTruncGame_le_cka (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (hS : CKACoins.Sound C) {J : Sc → Sc → Prop} (hJ : CKACorrect C J)
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (hJi : ∀ i ∈ initP.support, J i.2.1 i.2.2) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg)) (dec : W → W × ACDHdr Msg)
    (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS k : ℕ)
    (A : SMIDAdv (Msg × ℕ) W (ACDHdr Msg) Ct (ACDIDLeak Sc RK Sa Msg W)) :
    prTrue (smIDLogTruncGame (acdIDSM C R G D dec enc maxSkip maxStored) ΔFS ΔPCS k A)
        Heap.empty ≤
      CKA_Corrupt_Advantage C ΔFS ΔPCS
          (acdIDCKARed R G D dec enc maxSkip maxStored ΔFS ΔPCS k A) +
        prTrue (acdIDHopGame C R G D dec enc maxSkip maxStored ΔFS ΔPCS k (unifKeyRoot R) A)
          Heap.empty := by
  have h0 : smIDLogTruncGame (acdIDSM C R G D dec enc maxSkip maxStored) ΔFS ΔPCS k A =
      cka_corrupt_game C ΔFS ΔPCS false
        (acdIDCKARed R G D dec enc maxSkip maxStored ΔFS ΔPCS k A) := by
    rw [acdIDSM_logTruncGame_eq_hop C hJ initP hinit hJi, acdIDHopGame_eq_cka C hS initP hinit]
    simp only [ckaHopRoot, Bool.false_eq_true, ite_false]
  have h1 : acdIDHopGame C R G D dec enc maxSkip maxStored ΔFS ΔPCS k (unifKeyRoot R) A =
      cka_corrupt_game C ΔFS ΔPCS true
        (acdIDCKARed R G D dec enc maxSkip maxStored ΔFS ΔPCS k A) := by
    rw [acdIDHopGame_eq_cka C hS initP hinit]
    simp only [ckaHopRoot, ite_true]
  rw [h0, h1]
  unfold CKA_Corrupt_Advantage Advantage
  exact le_tsub_add.trans (add_le_add le_sup_left le_rfl)

end CKAHop

/-! ## The root hop -/

section RootHop

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [Fintype RK] [Nonempty RK] [Inhabited Msg] [DecidableEq Msg]
  [DecidableEq W] [DecidableEq Ct]

/-- The query of the base for the query `q` of the corruption game of party state `X`: the
header attached to the associated data by `enc`. -/
def acdIDBaseQuery (enc : ACDHdr Msg → W → W) (X : ACDIDX Sa Msg W) (q : SMQuery W) :
    SMQuery W :=
  q.mapMsg fun m => (m.1, enc (acdIDHdr X q.party) m.2)

/-- The answer and the state of the hop games after the query `q` of the corruption game,
answered by `y` over the base. -/
def acdIDSmF (G : PRGDef Sa (W × Sa)) (s : ACDIDHopSt Sc Msg RK Sa W Ct) (q : SMQuery W)
    (y : SMAns Sc Msg RK Sa Ct × SMSt Sc Msg RK Sa) :
    ACDIDAns Sc Msg RK Sa W Ct × ACDIDHopSt Sc Msg RK Sa W Ct :=
  (.sm ((acdIDAns (s.1.1.2.1 q.party) y.1).withHdr (acdIDHdr s.1.1.2 q.party)),
    (((y.2, acdIDXUpd G s.1.1.1.loc.rcv (ckaShadow s.1.1.1.ck) s.1.1.1.ck.msg s.1.1.2 q y.1),
      s.1.2.upd Prod.snd (ckaShadow s.1.1.1.ck) q
        ((acdIDAns (s.1.1.2.1 q.party) y.1).withHdr (acdIDHdr s.1.1.2 q.party))), s.2))

/-- The answer and the state of the hop games after a delivery. -/
def acdIDDlvF (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (maxSkip maxStored ΔFS ΔPCS k : ℕ) (s : ACDIDHopSt Sc Msg RK Sa W Ct) (p : CKAParty)
    (h : ACDHdr Msg) (ad : W) (c : Ct) :
    ACDIDAns Sc Msg RK Sa W Ct × ACDIDHopSt Sc Msg RK Sa W Ct :=
  (.dec (acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k s.1.1.1.loc.rcv (ckaShadow s.1.1.1.ck)
      s.1.1.2.1 s.1.2 p h ad c).1,
    (((s.1.1.1, ((acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k s.1.1.1.loc.rcv
        (ckaShadow s.1.1.1.ck) s.1.1.2.1 s.1.2 p h ad c).2.1.1, s.1.1.2.2)),
      (acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k s.1.1.1.loc.rcv (ckaShadow s.1.1.1.ck)
        s.1.1.2.1 s.1.2 p h ad c).2.1.2),
      s.2 || (acdIDDeliver G D maxSkip maxStored ΔFS ΔPCS k s.1.1.1.loc.rcv
        (ckaShadow s.1.1.1.ck) s.1.1.2.1 s.1.2 p h ad c).2.2))

omit [Fintype RK] [Nonempty RK] [Inhabited Msg] in
/-- A query of the corruption game through the gate in the hop step. -/
theorem acdIDHopStep_sm (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS t k : ℕ)
    (root : RK → Key → PMF (RK × Sa)) (s : ACDIDHopSt Sc Msg RK Sa W Ct) (q : SMQuery W)
    (hg : smIDGate s.1.2 (ckaShadow s.1.1.1.ck) q = true) :
    acdIDHopStep C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k root s (.sm q) =
      (smOracleOfAt C R G (aeadComapAD D dec) ΔFS ΔPCS t k false root s.1.1.1
        (acdIDBaseQuery enc s.1.1.2 q)).map (acdIDSmF G s q) := by
  simp only [acdIDHopStep, hg, ite_true]
  rfl

/-- The opening of the epoch `k` in the hop games: a ratchet query through the gate from a
state with the epoch `k` safe that opens the epoch `k`. -/
def acdIDRootCrit (ΔFS ΔPCS k : ℕ) (s : ACDIDHopSt Sc Msg RK Sa W Ct) :
    SMIDQuery W (ACDHdr Msg) Ct → Bool
  | .sm q => s.1.2.epochSafe ΔFS ΔPCS k && smIDGate s.1.2 (ckaShadow s.1.1.1.ck) q &&
      smCrit k s.1.1.1 q
  | .deliver _ _ _ _ => false

/-- **The simulator of the root hop of the forgery event at the epoch `k`** over `acdIDSM`: its
state is the state of the hop games; a query of the corruption game through the gate is
answered by `smRootImplAt`, which asks the root step at the opening of the epoch `k` to the
`prf` oracle of the PRF-PRNG game; a delivery is answered as in the hop games. -/
noncomputable def acdIDRootImpl (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS t k : ℕ)
    (s : ACDIDHopSt Sc Msg RK Sa W Ct) (d : SMIDQuery W (ACDHdr Msg) Ct) :
    OracleAdv (PPQuery RK Key) (RK × Sa)
      (ACDIDAns Sc Msg RK Sa W Ct × ACDIDHopSt Sc Msg RK Sa W Ct) :=
  if s.1.2.epochSafe ΔFS ΔPCS k then
    match d with
    | .sm q =>
      if smIDGate s.1.2 (ckaShadow s.1.1.1.ck) q then
        (smRootImplAt C R G (aeadComapAD D dec) ΔFS ΔPCS t k s.1.1.1
          (acdIDBaseQuery enc s.1.1.2 q)).bind fun y =>
            .ret (acdIDCut ΔFS ΔPCS k (acdIDSmF G s q y))
      else .ret (.sm .none, s)
    | .deliver p h ad c =>
      .ret (acdIDCut ΔFS ΔPCS k (acdIDDlvF G D maxSkip maxStored ΔFS ΔPCS k s p h ad c))
  else .ret (.dec none, s)

/-- The PRF-PRNG reduction of the forgery event at the epoch `k` over `acdIDSM` as an oracle
tree: it draws the challenge epoch `t` of the adversary from `tStar`, the CKA initialisation
from `initP` and a uniform root key, runs the adversary against `acdIDRootImpl` and outputs the
flag of a forgery. -/
noncomputable def acdIDRootTree (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS k : ℕ)
    (initP : PMF (Msg × Sc × Sc)) (tStar : PMF ℕ)
    (play : ℕ → Msg × ℕ → OracleAdv (SMIDQuery W (ACDHdr Msg) Ct) (ACDIDAns Sc Msg RK Sa W Ct)
      Bool) : OracleAdv (PPQuery RK Key) (RK × Sa) Bool :=
  .rand tStar fun t => .rand initP fun i => .rand (PMF.uniformFintype RK) fun rk =>
    (OracleAdv.simulate (acdIDRootImpl C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k)
      (play t (i.1, 0)) (((smInit i rk, acdIDXInit), SMIDAux.init (i.1, 0)), false)).bind
        fun r => .ret r.2.2

/-- **The PRF-PRNG reduction of the forgery event at the epoch `k`** over `acdIDSM`: the tree
`acdIDRootTree` at the challenge-epoch distribution and the interaction of `A`. -/
noncomputable def acdIDRootRed (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS k : ℕ)
    (initP : PMF (Msg × Sc × Sc))
    (A : SMIDAdv (Msg × ℕ) W (ACDHdr Msg) Ct (ACDIDLeak Sc RK Sa Msg W)) :
    OracleAdv (PPQuery RK Key) (RK × Sa) Bool :=
  acdIDRootTree C R G D dec enc maxSkip maxStored ΔFS ΔPCS k initP A.tStar A.play

omit [Fintype RK] [Nonempty RK] [Inhabited Msg] in
/-- A query of the corruption game through the gate in the simulator of the root hop, from a
safe state, is the query of `smRootImplAt`, completed and cut. -/
theorem acdIDRootImpl_simOracle (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS t k : ℕ)
    {U : Type} (O' : U → PPQuery RK Key → PMF ((RK × Sa) × U))
    (s : ACDIDHopSt Sc Msg RK Sa W Ct) (u : U) (q : SMQuery W)
    (hs : s.1.2.epochSafe ΔFS ΔPCS k = true) (hg : smIDGate s.1.2 (ckaShadow s.1.1.1.ck) q = true) :
    OracleAdv.simOracle (acdIDRootImpl C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k) O' (s, u)
        (.sm q) =
      (OracleAdv.simOracle (smRootImplAt C R G (aeadComapAD D dec) ΔFS ΔPCS t k) O' (s.1.1.1, u)
        (acdIDBaseQuery enc s.1.1.2 q)).map fun y =>
          ((acdIDCut ΔFS ΔPCS k (acdIDSmF G s q (y.1, y.2.1))).1,
            ((acdIDCut ΔFS ΔPCS k (acdIDSmF G s q (y.1, y.2.1))).2, y.2.2)) := by
  simp only [OracleAdv.simOracle, acdIDRootImpl, hs, hg, ite_true, OracleAdv.run_bind,
    OracleAdv.run_ret, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]

omit [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct] [Fintype RK]
  [Nonempty RK] [Inhabited Msg] [DecidableEq Msg] [DecidableEq W] [DecidableEq Ct] in
/-- The opening of an epoch by the query of the base is the opening by the query. -/
theorem smCrit_acdIDBaseQuery (enc : ACDHdr Msg → W → W) (X : ACDIDX Sa Msg W) (k : ℕ)
    (s : SMSt Sc Msg RK Sa) (q : SMQuery W) :
    smCrit k s (acdIDBaseQuery enc X q) = smCrit k s q := by
  cases q <;> rfl

omit [Fintype RK] [Nonempty RK] [Inhabited Msg] in
/-- The base states reached by a call of the hop oracle: the base state of the call, at a
delivery, outside the gate or with the epoch `k` outside the safe epochs, or a state reached by
`smOracleOfAt`. -/
theorem acdIDHopOracle_support (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS t k : ℕ)
    (root : RK → Key → PMF (RK × Sa)) (s : ACDIDHopSt Sc Msg RK Sa W Ct)
    (d : SMIDQuery W (ACDHdr Msg) Ct) (x)
    (hx : x ∈ (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k root s d).support) :
    (x.2.1.1.1 = s.1.1.1 ∧ ∀ q, d = .sm q →
        (s.1.2.epochSafe ΔFS ΔPCS k = false ∨ smIDGate s.1.2 (ckaShadow s.1.1.1.ck) q = false)) ∨
      ∃ q y, d = .sm q ∧ s.1.2.epochSafe ΔFS ΔPCS k = true ∧
        smIDGate s.1.2 (ckaShadow s.1.1.1.ck) q = true ∧
        y ∈ (smOracleOfAt C R G (aeadComapAD D dec) ΔFS ΔPCS t k false root s.1.1.1
          (acdIDBaseQuery enc s.1.1.2 q)).support ∧ x.2.1.1.1 = y.2 := by
  simp only [acdIDHopOracle, PMF.support_map, Set.mem_image] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  have hz2 : (acdIDCut ΔFS ΔPCS k z).2 = z.2 := by
    unfold acdIDCut
    split <;> rfl
  rw [hz2]
  split at hz
  · rename_i hs
    cases d with
    | sm q =>
      by_cases hg : smIDGate s.1.2 (ckaShadow s.1.1.1.ck) q = true
      · rw [acdIDHopStep_sm C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k root s q hg,
          PMF.support_map] at hz
        obtain ⟨w, hw, rfl⟩ := hz
        exact Or.inr ⟨q, w, rfl, hs, hg, hw, rfl⟩
      · simp only [acdIDHopStep, hg, Bool.false_eq_true, ite_false, PMF.support_pure,
          Set.mem_singleton_iff] at hz
        subst hz
        exact Or.inl ⟨rfl, fun q' h => by cases h; exact Or.inr (by simpa using hg)⟩
    | deliver p h ad c =>
      simp only [acdIDHopStep, PMF.support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact Or.inl ⟨rfl, fun q h => nomatch h⟩
  · rename_i hs
    simp only [PMF.support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl ⟨rfl, fun _ _ => Or.inl (by simpa using hs)⟩

omit [Fintype RK] [Nonempty RK] [Inhabited Msg] in
/-- Every call of the hop oracle keeps the epoch `k` opened. -/
theorem acdIDHopOracle_opened (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS t k : ℕ)
    (root : RK → Key → PMF (RK × Sa)) (s : ACDIDHopSt Sc Msg RK Sa W Ct)
    (d : SMIDQuery W (ACDHdr Msg) Ct) (hs : smOpened k s.1.1.1) (x)
    (hx : x ∈ (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k root s d).support) :
    smOpened k x.2.1.1.1 := by
  rcases acdIDHopOracle_support C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k root s d x hx with
    ⟨h, -⟩ | ⟨q, y, -, -, -, hy, h⟩
  · rw [h]; exact hs
  · rw [h]
    exact smOracleOfAt_opened C R G (aeadComapAD D dec) ΔFS ΔPCS t k false root s.1.1.1 _ hs y hy

omit [Fintype RK] [Nonempty RK] [Inhabited Msg] in
/-- The opening of the epoch `k` in the hop oracle leads to a state with the epoch `k`
opened. -/
theorem acdIDHopOracle_opened_of_crit (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS t k : ℕ)
    (root : RK → Key → PMF (RK × Sa)) (s : ACDIDHopSt Sc Msg RK Sa W Ct)
    (d : SMIDQuery W (ACDHdr Msg) Ct) (hc : acdIDRootCrit ΔFS ΔPCS k s d = true) (x)
    (hx : x ∈ (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k root s d).support) :
    smOpened k x.2.1.1.1 := by
  rcases acdIDHopOracle_support C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k root s d x hx with
    ⟨-, h⟩ | ⟨q, y, rfl, -, -, hy, h⟩
  · cases d with
    | sm q =>
      simp only [acdIDRootCrit, Bool.and_eq_true] at hc
      rcases h q rfl with h' | h' <;> simp [h'] at hc
    | deliver p h ad c => simp [acdIDRootCrit] at hc
  · simp only [acdIDRootCrit, Bool.and_eq_true] at hc
    rw [h]
    cases q with
    | ratchet p =>
      exact smOracleOf_opened_of_crit C R G (aeadComapAD D dec) ΔFS ΔPCS k false root s.1.1.1
        (.ratchet p) hc.2 y hy
    | _ => simp [smCrit] at hc

omit [Fintype RK] [Nonempty RK] [Inhabited Msg] in
/-- Away from the opening of the epoch `k`, the hop oracle does not depend on the root step at
the epoch `k`. -/
theorem acdIDHopOracle_root_congr (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS t k : ℕ)
    (root root' : RK → Key → PMF (RK × Sa)) (s : ACDIDHopSt Sc Msg RK Sa W Ct)
    (d : SMIDQuery W (ACDHdr Msg) Ct) (hc : acdIDRootCrit ΔFS ΔPCS k s d = false) :
    acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k root s d =
      acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k root' s d := by
  by_cases hs : s.1.2.epochSafe ΔFS ΔPCS k = true
  · cases d with
    | sm q =>
      by_cases hg : smIDGate s.1.2 (ckaShadow s.1.1.1.ck) q = true
      · have hq : smCrit k s.1.1.1 q = false := by simpa [acdIDRootCrit, hs, hg] using hc
        have he : smOracleOfAt C R G (aeadComapAD D dec) ΔFS ΔPCS t k false root s.1.1.1
            (acdIDBaseQuery enc s.1.1.2 q) = smOracleOfAt C R G (aeadComapAD D dec) ΔFS ΔPCS
              t k false root' s.1.1.1 (acdIDBaseQuery enc s.1.1.2 q) := by
          cases q with
          | ratchet p =>
            exact smOracleOf_root_congr C R G (aeadComapAD D dec) ΔFS ΔPCS k false root root'
              s.1.1.1 (.ratchet p) hq
          | _ => rfl
        simp only [acdIDHopOracle, hs, ite_true,
          acdIDHopStep_sm C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k _ s q hg, he]
      · simp [acdIDHopOracle, hs, acdIDHopStep, hg]
    | deliver p h ad c => rfl
  · simp only [acdIDHopOracle, hs, Bool.false_eq_true, ite_false]

omit [Fintype RK] [Nonempty RK] [Inhabited Msg] in
/-- Away from the opening of the epoch `k`, the simulator of the root hop asks no query and
answers as the hop oracle with any root step at the epoch `k`. -/
theorem acdIDRoot_step_noncrit (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS t k : ℕ)
    (root : RK → Key → PMF (RK × Sa)) {U : Type} (O' : U → PPQuery RK Key → PMF ((RK × Sa) × U))
    (s : ACDIDHopSt Sc Msg RK Sa W Ct) (u : U) (d : SMIDQuery W (ACDHdr Msg) Ct)
    (hc : acdIDRootCrit ΔFS ΔPCS k s d = false) :
    OracleAdv.simOracle (acdIDRootImpl C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k) O' (s, u) d =
      (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k root s d).map
        fun z => (z.1, (z.2, u)) := by
  by_cases hs : s.1.2.epochSafe ΔFS ΔPCS k = true
  · cases d with
    | sm q =>
      by_cases hg : smIDGate s.1.2 (ckaShadow s.1.1.1.ck) q = true
      · have hq : smCrit k s.1.1.1 (acdIDBaseQuery enc s.1.1.2 q) = false := by
          rw [smCrit_acdIDBaseQuery]
          simpa [acdIDRootCrit, hs, hg] using hc
        rw [acdIDRootImpl_simOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k O' s u q hs hg,
          smRootImplAt_step_noncrit C R G (aeadComapAD D dec) ΔFS ΔPCS t k root O' s.1.1.1 u _ hq]
        simp only [acdIDHopOracle, hs, ite_true,
          acdIDHopStep_sm C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k root s q hg, PMF.map_comp]
        rfl
      · simp [OracleAdv.simOracle, acdIDRootImpl, acdIDHopOracle, acdIDHopStep, hs, hg,
          PMF.pure_map, acdIDCut]
    | deliver p h ad c =>
      simp [OracleAdv.simOracle, acdIDRootImpl, acdIDHopOracle, acdIDHopStep, hs, PMF.pure_map,
        acdIDDlvF]
  · simp [OracleAdv.simOracle, acdIDRootImpl, acdIDHopOracle, hs, PMF.pure_map, acdIDCut]

variable [Fintype Sa] [Nonempty Sa] [DecidableEq RK] [DecidableEq Key]

omit [Inhabited Msg] in
/-- **The simulator of the root hop against the real PRF-PRNG game.** With the hidden input
`key`, each call of the hop oracle with the root step `fixedKeyRoot R key` at the epoch `k`,
with the PRF-PRNG state attached, is the call of `acdIDRootImpl` against the real PRF-PRNG
oracle. -/
theorem acdIDRoot_step_real (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS t k : ℕ)
    (rk' : RK) (key : Key) (s : ACDIDHopSt Sc Msg RK Sa W Ct) (d : SMIDQuery W (ACDHdr Msg) Ct) :
    (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k (fixedKeyRoot R key) s d).map
        (Prod.map id fun s => (s, (⟨rk', key, [], []⟩ : PPSt RK Key (RK × Sa)))) =
      OracleAdv.simOracle (acdIDRootImpl C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k)
        (ppOracle (rootFn R) false false) (s, ⟨rk', key, [], []⟩) d := by
  by_cases hs : s.1.2.epochSafe ΔFS ΔPCS k = true
  · cases d with
    | sm q =>
      by_cases hg : smIDGate s.1.2 (ckaShadow s.1.1.1.ck) q = true
      · rw [acdIDRootImpl_simOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k _ s _ q hs hg,
          ← smRootImplAt_step_real C R G (aeadComapAD D dec) ΔFS ΔPCS t k rk' key s.1.1.1 _]
        simp only [acdIDHopOracle, hs, ite_true,
          acdIDHopStep_sm C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k _ s q hg, PMF.map_comp]
        rfl
      · simp [OracleAdv.simOracle, acdIDRootImpl, acdIDHopOracle, acdIDHopStep, hs, hg,
          PMF.pure_map, acdIDCut]
    | deliver p h ad c =>
      simp [OracleAdv.simOracle, acdIDRootImpl, acdIDHopOracle, acdIDHopStep, hs, PMF.pure_map,
        acdIDDlvF]
      rfl
  · simp [OracleAdv.simOracle, acdIDRootImpl, acdIDHopOracle, hs, PMF.pure_map, acdIDCut]

omit [Inhabited Msg] in
/-- **The simulator of the root hop against the ideal PRF-PRNG game.** From a state whose table
of the `prf` oracle is empty unless the epoch `k` has been opened, each call of
`acdIDRootImpl` against the ideal PRF-PRNG oracle, with the PRF-PRNG state dropped, is the call
of the hop oracle with a uniform root output at the epoch `k`. -/
theorem acdIDRoot_step_ideal (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS t k : ℕ)
    (s : ACDIDHopSt Sc Msg RK Sa W Ct) (u : PPSt RK Key (RK × Sa))
    (hu : u.tR = [] ∨ smOpened k s.1.1.1) (d : SMIDQuery W (ACDHdr Msg) Ct) :
    (OracleAdv.simOracle (acdIDRootImpl C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k)
        (ppOracle (rootFn R) true true) (s, u) d).map (Prod.map id Prod.fst) =
      acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k unifRoot s d := by
  by_cases hs : s.1.2.epochSafe ΔFS ΔPCS k = true
  · cases d with
    | sm q =>
      by_cases hg : smIDGate s.1.2 (ckaShadow s.1.1.1.ck) q = true
      · rw [acdIDRootImpl_simOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k _ s u q hs hg,
          PMF.map_comp]
        simp only [acdIDHopOracle, hs, ite_true,
          acdIDHopStep_sm C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k _ s q hg]
        rw [← smRootImplAt_step_ideal C R G (aeadComapAD D dec) ΔFS ΔPCS t k s.1.1.1 u hu _]
        simp only [PMF.map_comp]
        rfl
      · simp [OracleAdv.simOracle, acdIDRootImpl, acdIDHopOracle, acdIDHopStep, hs, hg,
          PMF.pure_map, acdIDCut]
    | deliver p h ad c =>
      simp [OracleAdv.simOracle, acdIDRootImpl, acdIDHopOracle, acdIDHopStep, hs, PMF.pure_map,
        acdIDDlvF]
  · simp [OracleAdv.simOracle, acdIDRootImpl, acdIDHopOracle, hs, PMF.pure_map, acdIDCut]

omit [Inhabited Msg] in
/-- The simulator of the root hop against the ideal PRF-PRNG game keeps the invariant of
`acdIDRoot_step_ideal`. -/
theorem acdIDRoot_inv_ideal (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS t k : ℕ)
    (s : ACDIDHopSt Sc Msg RK Sa W Ct) (u : PPSt RK Key (RK × Sa))
    (hu : u.tR = [] ∨ smOpened k s.1.1.1) (d : SMIDQuery W (ACDHdr Msg) Ct) :
    ∀ y ∈ (OracleAdv.simOracle (acdIDRootImpl C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k)
        (ppOracle (rootFn R) true true) (s, u) d).support,
      y.2.2.tR = [] ∨ smOpened k y.2.1.1.1.1 := by
  intro y hy
  by_cases hc : acdIDRootCrit ΔFS ΔPCS k s d = true
  · have hm : (y.1, y.2.1) ∈ (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k
        unifRoot s d).support := by
      rw [← acdIDRoot_step_ideal C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k s u hu d,
        PMF.support_map]
      exact ⟨y, hy, rfl⟩
    exact Or.inr (acdIDHopOracle_opened_of_crit C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k
      unifRoot s d hc _ hm)
  · rw [acdIDRoot_step_noncrit C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k unifRoot _ s u d
      (by simpa using hc)] at hy
    simp only [PMF.support_map, Set.mem_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rcases hu with h | h
    · exact Or.inl h
    · exact Or.inr (acdIDHopOracle_opened C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k unifRoot
        s d h z hz)

variable [Fintype Key] [Nonempty Key]

omit [Fintype RK] [Nonempty RK] [Inhabited Msg] [Fintype Sa] [Nonempty Sa] [DecidableEq RK]
  [DecidableEq Key] in
/-- **Eager sampling of the key of the root step at the epoch `k`** in the hop oracle. -/
theorem acdIDHop_run_eager (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS t k : ℕ)
    {α : Type} (A : OracleAdv (SMIDQuery W (ACDHdr Msg) Ct) (ACDIDAns Sc Msg RK Sa W Ct) α)
    (s : ACDIDHopSt Sc Msg RK Sa W Ct) :
    OracleAdv.run (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k (unifKeyRoot R))
        A s =
      (PMF.uniformFintype Key).bind fun key =>
        OracleAdv.run (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k
          (fixedKeyRoot R key)) A s := by
  refine OracleAdv.run_eq_bind_eager _ _ (PMF.uniformFintype Key) (acdIDRootCrit ΔFS ΔPCS k)
    ?_ ?_ (fun s => smOpened k s.1.1.1) ?_ ?_ ?_ A s
  · intro s d hc
    cases d with
    | sm q =>
      simp only [acdIDRootCrit, Bool.and_eq_true] at hc
      obtain ⟨⟨hs, hg⟩, hq⟩ := hc
      cases q with
      | ratchet p =>
        have hroot : ∀ rk I, unifKeyRoot R rk I =
            (PMF.uniformFintype Key).bind fun v => fixedKeyRoot R v rk I := fun _ _ => rfl
        simp only [smCrit, Bool.and_eq_true] at hq
        have h : smOracleOfAt C R G (aeadComapAD D dec) ΔFS ΔPCS t k false (unifKeyRoot R)
            s.1.1.1 (acdIDBaseQuery enc s.1.1.2 (.ratchet p)) =
            (PMF.uniformFintype Key).bind fun v =>
              smOracleOfAt C R G (aeadComapAD D dec) ΔFS ΔPCS t k false (fixedKeyRoot R v)
                s.1.1.1 (acdIDBaseQuery enc s.1.1.2 (.ratchet p)) := by
          simp only [acdIDBaseQuery, SMQuery.mapMsg, smOracleOfAt, smOracleOf, hq.1, hq.2,
            ite_true, hroot, PMF.bind_bind]
          exact PMF.bind_comm _ _ _
        simp only [acdIDHopOracle, hs, ite_true,
          acdIDHopStep_sm C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k _ s _ hg, h, PMF.map_bind]
      | _ => simp [smCrit] at hq
    | deliver p h ad c => simp [acdIDRootCrit] at hc
  · intro v s d hc
    exact acdIDHopOracle_root_congr C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k _ _ s d hc
  · intro v s d hc x hx
    exact acdIDHopOracle_opened_of_crit C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k _ s d hc
      x hx
  · intro s d hs x hx
    exact acdIDHopOracle_opened C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k _ s d hs x hx
  · intro s d hs
    cases d with
    | sm q => simp [acdIDRootCrit, smCrit_of_opened k s.1.1.1 hs q]
    | deliver p h ad c => rfl

omit [Fintype Key] [Nonempty Key] [Fintype Sa] [Nonempty Sa] [DecidableEq RK]
  [DecidableEq Key] in
/-- Running the PRF-PRNG reduction of the forgery event against an oracle is running the
adversary against the composed oracle from the drawn initial state, with the flag of a forgery
as output. -/
theorem acdIDRootRed_run (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS k : ℕ)
    (initP : PMF (Msg × Sc × Sc))
    (A : SMIDAdv (Msg × ℕ) W (ACDHdr Msg) Ct (ACDIDLeak Sc RK Sa Msg W)) {U : Type}
    (O' : U → PPQuery RK Key → PMF ((RK × Sa) × U)) (u : U) :
    (OracleAdv.run O' (acdIDRootRed C R G D dec enc maxSkip maxStored ΔFS ΔPCS k initP A) u).map
        Prod.fst =
      A.tStar.bind fun t => initP.bind fun i => (PMF.uniformFintype RK).bind fun rk =>
        (OracleAdv.run (OracleAdv.simOracle
          (acdIDRootImpl C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k) O')
          (A.play t (i.1, 0)) ((((smInit i rk, acdIDXInit), SMIDAux.init (i.1, 0)), false),
            u)).map fun x => x.2.1.2 := by
  simp only [acdIDRootRed, acdIDRootTree, OracleAdv.run_rand, PMF.map_bind]
  refine congrArg _ (funext fun t => congrArg _ (funext fun i =>
    congrArg _ (funext fun rk => ?_)))
  rw [OracleAdv.run_bind, OracleAdv.run_simulate]
  simp [PMF.map_bind, PMF.bind_map, Function.comp_def, PMF.pure_map]
  rfl

omit [Fintype Key] [Nonempty Key] [Fintype Sa] [Nonempty Sa] [DecidableEq RK]
  [DecidableEq Key] in
/-- The hop game as the lift of a distribution: the challenge epoch, the CKA initialisation,
the root key and the run. -/
theorem acdIDHopGame_eq_liftPMF (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS k : ℕ)
    (root : RK → Key → PMF (RK × Sa))
    (A : SMIDAdv (Msg × ℕ) W (ACDHdr Msg) Ct (ACDIDLeak Sc RK Sa Msg W)) :
    acdIDHopGame C R G D dec enc maxSkip maxStored ΔFS ΔPCS k root A =
      liftPMF (A.tStar.bind fun t => initP.bind fun i => (PMF.uniformFintype RK).bind fun rk =>
        (OracleAdv.run (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k root)
          (A.play t (i.1, 0)) (((smInit i rk, acdIDXInit), SMIDAux.init (i.1, 0)), false)).map
            fun x => x.2.2) := by
  simp only [acdIDHopGame, hinit, sample_eq_liftPMF, liftPMF_bind_liftPMF]

/-- **The real side of the root hop** over `acdIDSM`: the real PRF-PRNG game of `acdIDRootRed`
is the hop game with the root KDF on a uniform key at the epoch `k`. -/
theorem acdIDRoot_real_eq (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS k : ℕ)
    (A : SMIDAdv (Msg × ℕ) W (ACDHdr Msg) Ct (ACDIDLeak Sc RK Sa Msg W)) :
    pp_game (rootFn R) false false
        (acdIDRootRed C R G D dec enc maxSkip maxStored ΔFS ΔPCS k initP A) =
      acdIDHopGame C R G D dec enc maxSkip maxStored ΔFS ΔPCS k (unifKeyRoot R) A := by
  rw [acdIDHopGame_eq_liftPMF C initP hinit]
  unfold pp_game
  congr 1
  have h1 : ∀ (rk' : RK) (key : Key),
      (OracleAdv.run (ppOracle (rootFn R) false false)
        (acdIDRootRed C R G D dec enc maxSkip maxStored ΔFS ΔPCS k initP A)
          ⟨rk', key, [], []⟩).map Prod.fst =
      A.tStar.bind fun t => initP.bind fun i => (PMF.uniformFintype RK).bind fun rk =>
        (OracleAdv.run (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k
          (fixedKeyRoot R key)) (A.play t (i.1, 0))
            (((smInit i rk, acdIDXInit), SMIDAux.init (i.1, 0)), false)).map fun x => x.2.2 := by
    intro rk' key
    rw [acdIDRootRed_run]
    refine congrArg _ (funext fun t => congrArg _ (funext fun i =>
      congrArg _ (funext fun rk => ?_)))
    rw [← OracleAdv.run_map_state _ _ (fun s => (s, (⟨rk', key, [], []⟩ : PPSt RK Key (RK × Sa))))
      (acdIDRoot_step_real C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k rk' key),
      PMF.map_comp]
    rfl
  simp only [h1, PMF.bind_const]
  have h2 : ∀ (t : ℕ) (i : Msg × Sc × Sc) (rk : RK),
      (OracleAdv.run (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k
        (unifKeyRoot R)) (A.play t (i.1, 0))
          (((smInit i rk, acdIDXInit), SMIDAux.init (i.1, 0)), false)).map (fun x => x.2.2) =
      (PMF.uniformFintype Key).bind fun key =>
        (OracleAdv.run (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k
          (fixedKeyRoot R key)) (A.play t (i.1, 0))
            (((smInit i rk, acdIDXInit), SMIDAux.init (i.1, 0)), false)).map fun x => x.2.2 := by
    intro t i rk
    rw [acdIDHop_run_eager, PMF.map_bind]
  simp only [h2, PMF.bind_comm (PMF.uniformFintype Key)]

/-- **The ideal side of the root hop** over `acdIDSM`: the ideal PRF-PRNG game of
`acdIDRootRed` is the hop game with a uniform root output at the epoch `k`. -/
theorem acdIDRoot_ideal_eq (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS k : ℕ)
    (A : SMIDAdv (Msg × ℕ) W (ACDHdr Msg) Ct (ACDIDLeak Sc RK Sa Msg W)) :
    pp_game (rootFn R) true true
        (acdIDRootRed C R G D dec enc maxSkip maxStored ΔFS ΔPCS k initP A) =
      acdIDHopGame C R G D dec enc maxSkip maxStored ΔFS ΔPCS k unifRoot A := by
  rw [acdIDHopGame_eq_liftPMF C initP hinit]
  unfold pp_game
  congr 1
  have h1 : ∀ (rk' : RK) (key : Key),
      (OracleAdv.run (ppOracle (rootFn R) true true)
        (acdIDRootRed C R G D dec enc maxSkip maxStored ΔFS ΔPCS k initP A)
          ⟨rk', key, [], []⟩).map Prod.fst =
      A.tStar.bind fun t => initP.bind fun i => (PMF.uniformFintype RK).bind fun rk =>
        (OracleAdv.run (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k unifRoot)
          (A.play t (i.1, 0)) (((smInit i rk, acdIDXInit), SMIDAux.init (i.1, 0)), false)).map
            fun x => x.2.2 := by
    intro rk' key
    rw [acdIDRootRed_run]
    refine congrArg _ (funext fun t => congrArg _ (funext fun i =>
      congrArg _ (funext fun rk => ?_)))
    have h := OracleAdv.run_map_state_of_inv _
      (acdIDHopOracle C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k unifRoot)
      Prod.fst (fun x => x.2.tR = [] ∨ smOpened k x.1.1.1.1)
      (fun x d hx => acdIDRoot_inv_ideal C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k x.1 x.2
        hx d)
      (fun x d hx => acdIDRoot_step_ideal C R G D dec enc maxSkip maxStored ΔFS ΔPCS t k x.1 x.2
        hx d) (A.play t (i.1, 0))
      ((((smInit i rk, acdIDXInit), SMIDAux.init (i.1, 0)), false),
        (⟨rk', key, [], []⟩ : PPSt RK Key (RK × Sa))) (Or.inl rfl)
    refine Eq.trans ?_ (congrArg (PMF.map fun x => x.2.2) h)
    rw [PMF.map_comp]
    rfl
  simp only [h1, PMF.bind_const]

/-- **The root hop of the forgery event at the epoch `k`** over `acdIDSM`: the probability of a
forgery at the epoch `k` in the hop game with the root KDF on a uniform key at the epoch `k` is
at most the PRF-PRNG advantage of `R` at `acdIDRootRed … k initP A` plus the probability of a
forgery in the hop game with a uniform root output at the epoch `k`. -/
theorem acdIDHopGame_le_root (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg))
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS k : ℕ)
    (A : SMIDAdv (Msg × ℕ) W (ACDHdr Msg) Ct (ACDIDLeak Sc RK Sa Msg W)) :
    prTrue (acdIDHopGame C R G D dec enc maxSkip maxStored ΔFS ΔPCS k (unifKeyRoot R) A)
        Heap.empty ≤
      PRFPRNG_Advantage R (acdIDRootRed C R G D dec enc maxSkip maxStored ΔFS ΔPCS k initP A) +
        prTrue (acdIDHopGame C R G D dec enc maxSkip maxStored ΔFS ΔPCS k unifRoot A)
          Heap.empty := by
  rw [← acdIDRoot_real_eq C initP hinit, ← acdIDRoot_ideal_eq C initP hinit]
  unfold PRFPRNG_Advantage Advantage
  exact le_tsub_add.trans (add_le_add le_sup_left le_rfl)

end RootHop

/-! ## Integrity up to the hop game with a uniform root output -/

section Assembly

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [Fintype RK] [Nonempty RK] [Inhabited Msg] [DecidableEq Msg]
  [DecidableEq W] [DecidableEq Ct] [Fintype Sa] [Nonempty Sa] [DecidableEq RK] [DecidableEq Key]
  [Fintype Key] [Nonempty Key]

/-- **Integrity of the ACD construction with headers up to the hop games with a uniform root
output.** For a CKA correct along `J` with a sound explicit-randomness sending algorithm, an
initialisation that is the lift of `initP`, initial states related by `J`, and an adversary `A`
whose interactions ask at most `N` queries, the integrity advantage of `A` against
`acdIDSM C R G D dec enc maxSkip maxStored` is at most the sum over the epochs `k < N` of the
CKA corruption advantage of `acdIDCKARed … k A`, the PRF-PRNG advantage of `R` at
`acdIDRootRed … k initP A`, and the probability of a forgery at the epoch `k` in the hop game
whose root step at the opening of the epoch `k` outputs a uniform root key and chain. -/
theorem acdIDSM_intAdvantage_le_unifRoot (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (hS : CKACoins.Sound C) {J : Sc → Sc → Prop} (hJ : CKACorrect C J)
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (hJi : ∀ i ∈ initP.support, J i.2.1 i.2.2) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct (W × ACDHdr Msg)) (dec : W → W × ACDHdr Msg)
    (enc : ACDHdr Msg → W → W) (maxSkip maxStored ΔFS ΔPCS N : ℕ)
    (A : SMIDAdv (Msg × ℕ) W (ACDHdr Msg) Ct (ACDIDLeak Sc RK Sa Msg W))
    (hA : ∀ t pub, (A.play t pub).IsQueryBound N) :
    (acdIDSM C R G D dec enc maxSkip maxStored).intAdvantage ΔFS ΔPCS A ≤
      ∑ k ∈ Finset.range N,
        (CKA_Corrupt_Advantage C ΔFS ΔPCS
            (acdIDCKARed R G D dec enc maxSkip maxStored ΔFS ΔPCS k A) +
          PRFPRNG_Advantage R
            (acdIDRootRed C R G D dec enc maxSkip maxStored ΔFS ΔPCS k initP A) +
          prTrue (acdIDHopGame C R G D dec enc maxSkip maxStored ΔFS ΔPCS k unifRoot A)
            Heap.empty) := by
  refine (SMIDScheme.intAdvantage_le_sum_logBad _ ΔFS ΔPCS N A hA).trans
    (Finset.sum_le_sum fun k _ => ?_)
  rw [← smIDLogTruncGame_eq, add_assoc]
  exact (acdIDSM_logTruncGame_le_cka C hS hJ initP hinit hJi R G D dec enc maxSkip maxStored
    ΔFS ΔPCS k A).trans (add_le_add le_rfl
      (acdIDHopGame_le_root C initP hinit R G D dec enc maxSkip maxStored ΔFS ΔPCS k A))

end Assembly

end CatCrypt.Crypto.Messaging
