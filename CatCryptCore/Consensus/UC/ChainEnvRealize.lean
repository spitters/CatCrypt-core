/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.UC.ChainEnv

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# PoS-NSB driven by an environment realizes `F_Tree`

The protocol `chainRealE` of `CatCryptCore.Consensus.UC.ChainEnv`, driven by an environment
that sends honest transactions, phase entries with adversary indices and hash queries, realizes
the tree functionality `chainFE` with the simulator `chainSimE`, with bound the failure bound
`posFailE … Z` of `pos_nsb_securityE` for every environment `Z`.

The activations of the environment that run no phase repeat the view of the last phase, so the
tree trace of a run is the tree trace `XT` of the execution of the final log read at the number
of phase entries of each prefix of the log: a monotone reindexing that advances by at most one
phase per activation, except that a first activation that runs a phase skips the view of phase
`0`, whose round and observer position are those of phase `1`.

## Main definitions

* `stViewE`, `chainInitE`, `chainFE` — the stored view of a state, the initial state, and the
  functionality `F_Tree^P` over the states of `chainSimE`, with the properties `chainP` of
  `CatCryptCore.Consensus.UC.Chain`.
* `TrInvE` — the views along a trace are those of the prefixes of a log.

## Main results

* `fTreeGuard_reindex` — the guard of `F_Tree^P` with `P = chainP` is preserved by a monotone
  reindexing of times that starts at `0`, advances the round by at most one per step, and starts
  each new round at a time that starts a new round of the reindexed trace with a position of the
  observer at least as long.
* `guard_trueE` — on a log on which `GoodE` holds, the guard holds on every trace of positive
  length whose views are those of the prefixes of the log.
* `prBad_le_prFinal_of_det` — for a deterministic system, a bad flag that implies a persistent
  property of the states has at most the probability that the final state satisfies a property
  implied by it.
* `guardFailE_le` — the guard fails on the run of `chainSimE` with probability at most
  `posFailE … Z`.
* `chain_realizesE` (headline) — `chainRealE` realizes `ideal (chainFE …) (chainSimE …)` with
  bound `posFailE … Z`.
-/

namespace CatCryptCore.Consensus.UC.ChainEnv

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent CatCrypt.NonUniform
open CatCryptCore.Consensus.UC.FTree CatCryptCore.Consensus.UC.Chain
open CatCrypt.Crypto.Signatures CatCrypt.Crypto.Assumptions
open PoSNSB Parameters BlockParameters Corruption Execution ClockNet
open scoped ENNReal

/-! ## Reindexing tree traces -/

section Reindex

variable {Party Blk : Type}

/-- A step of the reindexing that advances by at most one time keeps the round step. -/
theorem round_le_of_step (U : TreeTrace Party Blk) (hU : U.RoundStep) {a b : ℕ} (hab : a ≤ b)
    (hb : b ≤ a + 1) : (U.st b).round ≤ (U.st a).round + 1 := by
  rcases (show b = a ∨ b = a + 1 by omega) with rfl | rfl
  · omega
  · exact hU a

/-- A step of the reindexing that advances by at most one time and increases the round reaches a
time that starts a new round. -/
theorem newRound_of_step (U : TreeTrace Party Blk) (o : Party) {a b : ℕ} (hab : a ≤ b)
    (hb : b ≤ a + 1) (h : (U.st a).round < (U.st b).round) :
    ∃ s ≤ b, NewRound U s ∧ (U.st s).round = (U.st b).round ∧
      ((U.st b).pos o).length ≤ ((U.st s).pos o).length := by
  rcases (show b = a ∨ b = a + 1 by omega) with rfl | rfl
  · exact absurd h (lt_irrefl _)
  · exact ⟨a + 1, le_rfl, ⟨a, rfl, h⟩, rfl, le_rfl⟩

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ} (P : Protocol Tx Hash np n Hz)

/-- **Reindexing preserves the guard of `F_Tree^P`.** Let the tree trace `U` satisfy the guard
of `F_Tree^P` with `P = chainP`, and let `f` be monotone with `f 0 = 0`, such that the round of
`U` at `f (t + 1)` is at most one more than at `f t`, and every increase of the round from `f t`
to `f (t + 1)` reaches it at a time `s ≤ f (t + 1)` that starts a new round of `U`, with the same
round and a position of the observer `none` at least as long as at `f (t + 1)`. Then the trace
`t ↦ U.st (f t)` satisfies the guard. -/
theorem fTreeGuard_reindex (ν : PMF SlotKind) (d w : ℕ) (ε : ℝ)
    (U : TreeTrace (Option (Fin np)) (Block Tx Hash (Fin np))) (f : ℕ → ℕ)
    (hU : FTreeGuard (slotTree P) (chainP P ν d w ε) U) (hf0 : f 0 = 0) (hmono : Monotone f)
    (hround : ∀ t, (U.st (f (t + 1))).round ≤ (U.st (f t)).round + 1)
    (hnew : ∀ t, (U.st (f t)).round < (U.st (f (t + 1))).round →
      ∃ s ≤ f (t + 1), NewRound U s ∧ (U.st s).round = (U.st (f (t + 1))).round ∧
        ((U.st (f (t + 1))).pos none).length ≤ ((U.st s).pos none).length) :
    FTreeGuard (slotTree P) (chainP P ν d w ε) ⟨U.honest, fun t => U.st (f t)⟩ := by
  obtain ⟨⟨hTG, hPT, hCT, hRM⟩, hP, hAg⟩ := hU
  simp only [chainP, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hP
  obtain ⟨hCG, hCQ, hCP, hPN, hL⟩ := hP
  refine ⟨⟨fun p t t' hp h => hTG p _ _ hp (hmono h), fun p t hp => hPT p _ hp,
    fun p t hp => hCT p _ hp, fun t t' h => hRM _ _ (hmono h)⟩, ?_,
    fun p q t t' b b' i j hp hq hb hb' => hAg p q _ _ b b' i j hp hq hb hb'⟩
  simp only [chainP, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨?_, fun t p hp => hCQ (f t) p hp, fun t₁ t₂ k p₁ p₂ ht => hCP _ _ k p₁ p₂ (hmono ht),
    fun p q t t' hp hq ht => hPN p q _ _ hp hq (hmono ht), ?_⟩
  · rintro t₁ t₂ ht ⟨t₀, rfl, hlt⟩ hd w' hw'
    obtain ⟨s, hs, hNs, hrs, hls⟩ := hnew t₀ hlt
    have h := hCG s (f t₂) (hs.trans (hmono ht)) hNs (by rw [hrs]; exact hd) w'
      (by rw [hrs]; exact hw')
    exact (Nat.add_le_add_right hls w').trans h
  · exact ⟨fun p t a hp => hL.growth p (f t) a hp, fun p t hp => hL.decreasing p (f t) hp,
      fun p t hp => hL.genesis_mem p (f t) hp, hL.genesis_slot, fun p t hp => hL.inTree p (f t) hp,
      by show (U.st (f 0)).round = 0; rw [hf0]; exact hL.round_zero, hround⟩

end Reindex

/-! ## Bad flags of deterministic systems -/

section Det

variable {τ ζ E O : Type}

/-- **Bad flag of a deterministic system.** Let `Inv` be an invariant of the deterministic steps
of `S`, let `B` be a property of the states preserved by the steps from invariant states, implied
by `bad` on invariant states, and implying `q` on invariant states. Then the bad flag is set at
the end of the run with at most the probability that the final state satisfies `q`. -/
theorem prBad_le_prFinal_of_det (S : Sys τ E O) (bad q : τ → Bool) (Inv B : τ → Prop)
    (hinit : Inv S.init)
    (hstep : ∀ t e, Inv t → ∃ p, S.step t e = SPComp.pure p ∧ Inv p.1 ∧ (B t → B p.1))
    (hbad : ∀ t, Inv t → bad t = true → B t) (hq : ∀ t, Inv t → B t → q t = true)
    (Z : Env (Strat ζ E O) ζ) : prBad S bad Z ≤ prFinal S q Z := by
  have key : ∀ (n : ℕ) (z : ζ) (t : τ) (b b' : Bool) (h : Heap), Inv t → (b = true → B t) →
      prTrue (SPComp.bind (loop S bad Z.input n (z, t, b)) fun c => SPComp.pure c.2.2) h ≤
        prTrue (SPComp.bind (loop S (fun _ => false) Z.input n (z, t, b')) fun c =>
          SPComp.pure (q c.2.1)) h := by
    intro n
    induction n with
    | zero =>
      intro z t b b' h ht hb
      simp only [loop, SPComp.pure_bind, prTrue_pure]
      cases b
      · simp
      · simp [hq t ht (hb rfl)]
    | succ n ih =>
      intro z t b b' h ht hb
      simp only [loop, SPComp.bind_assoc]
      refine prTrue_bind_le_of_le _ _ _ _ fun a h₁ => ?_
      obtain ⟨p, hp, hp1, hp2⟩ := hstep t a.2 ht
      rw [hp, SPComp.pure_bind, SPComp.pure_bind]
      refine prTrue_bind_le_of_le _ _ _ _ fun z' h₂ => ih _ _ _ _ _ hp1 fun hb' => ?_
      cases hb0 : b
      · rw [hb0, Bool.false_or] at hb'
        exact hbad _ hp1 hb'
      · exact hp2 (hb hb0)
  unfold prBad prFinal run
  exact key _ _ _ _ _ _ hinit (hbad _ hinit)

/-- The final state of the run of the monitored system is that of the system. -/
theorem prFinal_monitor (π : Sys τ E O) (G : Trace τ E O → Bool) (q : τ → Bool)
    (Z : Env (Strat ζ E O) ζ) :
    prFinal (monitor π G) (fun m => q m.1) Z = prFinal π q Z := by
  unfold prFinal run
  have h := loop_map (monitor π G) π Prod.fst (fun _ => false) (fun _ => false) Z.input
    (fun t e => by simp [monitor, SPComp.map, SPComp.bind_assoc]) (fun _ => rfl)
    Z.input.rounds (Z.input.init, (monitor π G).init, false)
  calc _ = prTrue (SPComp.bind (SPComp.map (fun c => (c.1, c.2.1.1, c.2.2))
        (loop (monitor π G) (fun _ => false) Z.input Z.input.rounds
          (Z.input.init, (monitor π G).init, false))) fun c => SPComp.pure (q c.2.1)) Z.heap := by
        simp [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    _ = _ := by rw [h]; rfl

end Det

/-! ## The views of the first round -/

section FirstRound

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ} {PK SK Sig : Type}
  (P : Protocol Tx Hash np n Hz) (Sch : PSigScheme (Block Tx Hash (Fin np)) PK SK Sig)
  [Sch.Deterministic] (A : Adversary Tx Hash np n Hz PK Sig) (Tree : TreeFamily P)

/-- In the first three phases the round is `1`. -/
theorem phaseView_round_of_lt (K : ℕ) (ω : Seed Tx Hash np n Hz PK SK) {j : ℕ} (hj : j < 3) :
    (phaseView P Sch A Tree K ω j).round = 1 :=
  (sTrace_clock Sch P ω A false (min j K)).1.trans (by omega)

/-- In the first three phases the position of the observer is the genesis block. -/
theorem phaseView_pos_none_of_lt (K : ℕ) (ω : Seed Tx Hash np n Hz PK SK)
    {j : ℕ} (hj : j < 3) : (phaseView P Sch A Tree K ω j).pos none = [P.GB] := by
  let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec Sch false P ω A
  have ht : (sTrace Sch P ω A false (min j K)).t_now = 1 :=
    (sTrace_clock Sch P ω A false (min j K)).1.trans (by omega)
  show (Tree ω.L ω.f).bestChain ((sTrace Sch P ω A false (min j K)).t_now - 1) _ = _
  rw [ht]
  exact valid_chain_le_gb ((Tree ω.L ω.f).best_chain_valid _ _) fun b hb =>
    (best_chain_time _ _ _ b hb).trans (Nat.zero_le _)

end FirstRound

/-! ## The functionality and the guard -/

section Guard

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ} {PK SK Sig : Type}
  (P : Protocol Tx Hash np n Hz) (Sch : PSigScheme (Block Tx Hash (Fin np)) PK SK Sig)
  [Sch.Deterministic] {X S : Type} (F : AdvFamily X S Tx Hash np n Hz PK Sig) (x₀ : X)
  (dt : Slot → Fin np → Tx) (Tree : TreeFamily P)
  (H : HashScheme) (cd : H.Codec (BlockDom Tx Hash np Hz) Hash)

/-- The stored view of a state of the protocol driven by an environment. -/
def stViewE (s : SimStE Tx Hash np n Hz PK SK X) :
    TreeView (Option (Fin np)) (Block Tx Hash (Fin np)) :=
  s.1.2.2.2.1

/-- The initial state of the protocol driven by an environment with the ideal clock and
network: no seed, the empty log, no phase entry, the initial view `startView`, no leakage. -/
noncomputable def chainInitE (Δ : ℕ) : SimStE Tx Hash np n Hz PK SK X :=
  ((none, [], 0, startView P, none), (ideal (clockNetF (M := Unit) H₁ Δ) (clockNet H₁ Δ).proto).init)

/-- **The functionality** `F_Tree^P` over the states of the protocol driven by an environment,
with the stored view (`stViewE`), honest parties `honestP`, the slot tree, the properties
`chainP`, and exploded output `((0, initView), none)`. It depends on neither the adversary
family nor the tree family. -/
noncomputable def chainFE (Δ : ℕ) (ν : PMF SlotKind) (d w : ℕ) (ε : ℝ) :
    TFunc (SimStE Tx Hash np n Hz PK SK X) (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np) :=
  fTree stViewE honestP (slotTree P) (chainP P ν d w ε) (chainInitE P Δ)
    (((0, initView), none) : EnvOut Tx Hash np)

theorem chainSimω_init (K Δ : ℕ) (ω : Seed Tx Hash np n Hz PK SK) :
    (chainSimω P Sch F x₀ dt Tree K Δ ω).init = chainInitE P Δ := rfl

theorem chainSimE_init (K : ℕ) (μ : PMF (Option (Fin np))) (W Δ : ℕ) :
    (chainSimE P Sch F x₀ dt Tree H cd K μ W Δ).init = chainInitE P Δ := rfl

/-- The views along the trace `tr` are those of the prefixes of the log `log` for the seed `ω`:
at time `t ≠ 0` the view after the phase entries of the first `t` entries of the log. -/
def TrInvE (K Δ : ℕ) (ω : Seed Tx Hash np n Hz PK SK) (log : List (LogEvOf X Tx Hash np Hz))
    (tr : Trace (SimStE Tx Hash np n Hz PK SK X) (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) :
    Prop :=
  ∀ t ≤ tr.length, stViewE (stAt (chainInitE P Δ) tr t) =
    if t = 0 then startView P else viewE P Sch F x₀ dt Tree K ω (log.take t) (steps (log.take t)).length

theorem steps_length_append_singleton (log : List (LogEvOf X Tx Hash np Hz))
    (e : EnvEv Tx Hash np Hz X) :
    (steps (log ++ [e])).length = phaseNext (steps log).length e := by
  rcases e with e | (x | d) <;> simp [steps, stepOf, phaseNext]

theorem steps_take_mono (log : List (LogEvOf X Tx Hash np Hz)) {a b : ℕ} (h : a ≤ b) :
    (steps (log.take a)).length ≤ (steps (log.take b)).length :=
  ((List.take_prefix_take_left h).filterMap stepOf).length_le

theorem steps_take_succ_le (log : List (LogEvOf X Tx Hash np Hz)) (t : ℕ) :
    (steps (log.take (t + 1))).length ≤ (steps (log.take t)).length + 1 := by
  rw [List.take_add_one]
  simp only [steps, List.filterMap_append, List.length_append]
  rcases log[t]? with _ | e
  · simp
  · rcases e with e | (x | d) <;> simp [stepOf, List.filterMap_cons]

theorem steps_take_le (log : List (LogEvOf X Tx Hash np Hz)) (t : ℕ) :
    (steps (log.take t)).length ≤ log.length :=
  (List.length_filterMap_le _ _).trans (List.length_take_le' _ _)

/-- **The guard on good logs.** Let every honest party be an initial party, let the genesis block
have slot `0`, and let `4 ≤ w` unless `K + 1 < d + 2`. If `GoodE` holds for the seed `ω` and the
log `log`, the guard of `chainFE` holds on every trace of positive length and of the length of
the log whose views are those of the prefixes of the log (`TrInvE`). -/
theorem guard_trueE (K Δ : ℕ) (ν : PMF SlotKind) (d w : ℕ) (ε : ℝ)
    (hIP : ∀ p : Fin np, CorruptionStatus p = .Honest → p ∈ P.IP) (hGB : P.GB.sl = 0)
    (hw4 : K + 1 < d + 2 ∨ 4 ≤ w) (ω : Seed Tx Hash np n Hz PK SK)
    (log : List (LogEvOf X Tx Hash np Hz)) (hG : GoodE P Sch F x₀ dt Tree ν K d w ε ω log)
    (tr : Trace (SimStE Tx Hash np n Hz PK SK X) (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np))
    (hlen : 1 ≤ tr.length) (hl : log.length = tr.length)
    (htr : TrInvE P Sch F x₀ dt Tree K Δ ω log tr) :
    (chainFE P Δ ν d w ε).guard tr = true := by
  rw [chainFE, fTree_guard_iff]
  set P' := P.withTx (txOf dt log)
  set A' := F.at (scriptOfD x₀ log)
  set U := XT P' Sch A' Tree K ω (tr.length + 1) with hUdef
  set f : ℕ → ℕ := fun t => if t = 0 then 0 else (steps (log.take t)).length + 1 with hfdef
  have hU : FTreeGuard (slotTree P) (chainP P ν d w ε) U :=
    guard_of_good P' Sch A' Tree K ν d w ε hIP hGB hw4 ω hG (by omega)
  have hLU : U.LiveTrace (slotTree P) Block.sl (d + 2) := hU.2.1 (fun X => X.LiveTrace (slotTree P) Block.sl (d + 2)) (by simp [chainP])
  have hU0 : U.st 0 = startView P := by simp only [hUdef, XT, ite_true]; rfl
  have hUs : ∀ j ≤ tr.length, U.st (j + 1) = phaseView P' Sch A' Tree K ω j := by
    intro j hj
    simp only [hUdef, XT, Nat.add_one_ne_zero, ite_false]
    congr 1
    omega
  have hj1 : (steps (log.take 1)).length ≤ 1 := by
    simpa [steps] using steps_take_succ_le log 0
  have hfs : ∀ t, t ≠ 0 → U.st (f t) = phaseView P' Sch A' Tree K ω (steps (log.take t)).length :=
    fun t ht => by
      simp only [hfdef, ite_eq_right ht]
      exact hUs _ ((steps_take_le log t).trans hl.le)
  have hmono : Monotone f := by
    intro a b hab
    simp only [hfdef]
    split_ifs with ha hb hb
    · exact le_rfl
    · exact Nat.zero_le _
    · omega
    · exact Nat.add_le_add_right (steps_take_mono log hab) 1
  have e : traceOf stViewE honestP (chainInitE P Δ) tr = ⟨U.honest, fun t => U.st (f t)⟩ := by
    simp only [traceOf, TreeTrace.mk.injEq]
    refine ⟨rfl, funext fun t => ?_⟩
    rw [← stAt_min_length, htr _ (min_le_right _ _)]
    by_cases ht : t = 0
    · subst ht
      simp [hfdef, hU0]
    · rw [ite_eq_right (by omega), hfs t ht]
      have htk : log.take (min t tr.length) = log.take t := by
        rw [← hl]
        rcases le_total t log.length with h | h
        · rw [min_eq_left h]
        · rw [min_eq_right h, List.take_of_length_le h, List.take_length]
      rw [htk]
      have hv := viewE_append P Sch F x₀ dt Tree K ω (log := log.take t) le_rfl (log.drop t)
      rw [List.take_append_drop] at hv
      rw [← hv]
      rfl
  have hround0 : (U.st (f 1)).round ≤ (U.st (f 0)).round + 1 := by
    rw [hfs 1 one_ne_zero, show f 0 = 0 from rfl, hU0,
      phaseView_round_of_lt P' Sch A' Tree K ω (by omega)]
    simp [startView]
  have hnew0 : (U.st (f 0)).round < (U.st (f 1)).round →
      ∃ s ≤ f 1, NewRound U s ∧ (U.st s).round = (U.st (f 1)).round ∧
        ((U.st (f 1)).pos none).length ≤ ((U.st s).pos none).length := by
    intro _
    have h1 : U.st 1 = phaseView P' Sch A' Tree K ω 0 := hUs 0 (Nat.zero_le _)
    have hr1 : (U.st 1).round = 1 := by rw [h1]; exact phaseView_round_of_lt P' Sch A' Tree K ω (by omega)
    refine ⟨1, ?_, ⟨0, rfl, ?_⟩, ?_, ?_⟩
    · simp [hfdef]
    · rw [hU0, hr1]; simp [startView]
    · rw [hr1, hfs 1 one_ne_zero, phaseView_round_of_lt P' Sch A' Tree K ω (by omega)]
    · rw [h1, hfs 1 one_ne_zero, phaseView_pos_none_of_lt P' Sch A' Tree K ω (by omega),
        phaseView_pos_none_of_lt P' Sch A' Tree K ω (by omega)]
  have hstep : ∀ t, t ≠ 0 → f t ≤ f (t + 1) ∧ f (t + 1) ≤ f t + 1 := by
    intro t ht
    simp only [hfdef, ite_eq_right ht, Nat.add_one_ne_zero, ite_false]
    exact ⟨Nat.add_le_add_right (steps_take_mono log (Nat.le_succ t)) 1,
      Nat.add_le_add_right (steps_take_succ_le log t) 1⟩
  rw [e]
  refine fTreeGuard_reindex P ν d w ε U f hU rfl hmono (fun t => ?_) (fun t => ?_)
  · rcases Nat.eq_zero_or_pos t with rfl | ht
    · exact hround0
    · exact round_le_of_step U hLU.round_step (hstep t (by omega)).1 (hstep t (by omega)).2
  · rcases Nat.eq_zero_or_pos t with rfl | ht
    · exact hnew0
    · exact newRound_of_step U none (hstep t (by omega)).1 (hstep t (by omega)).2

/-! ## The guard fails with at most the failure probability -/

/-- The invariant of the protocol for the seed `ω` with the monitor of the guard of `chainFE`:
the seed is unset or `ω`, the log has the length of the trace, the counter is the number of
phase entries of the log, the views along the trace are those of the prefixes of the log
(`TrInvE`), and a set flag means that the trace is nonempty and fails the guard. -/
def MInvE (K Δ : ℕ) (ν : PMF SlotKind) (d w : ℕ) (ε : ℝ) (ω : Seed Tx Hash np n Hz PK SK)
    (m : SimStE Tx Hash np n Hz PK SK X ×
      Trace (SimStE Tx Hash np n Hz PK SK X) (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np) × Bool) :
    Prop :=
  m.1.1.1.getD ω = ω ∧ m.1.1.2.1.length = m.2.1.length ∧
    m.1.1.2.2.1 = (steps m.1.1.2.1).length ∧ TrInvE P Sch F x₀ dt Tree K Δ ω m.1.1.2.1 m.2.1 ∧
    (m.2.2 = true → m.2.1 ≠ [] ∧ (chainFE P Δ ν d w ε).guard m.2.1 = false)

/-- The steps of the monitored protocol for the seed `ω` are deterministic and keep `MInvE`. -/
theorem mInvE_step (K Δ : ℕ) (ν : PMF SlotKind) (d w : ℕ) (ε : ℝ) (ω : Seed Tx Hash np n Hz PK SK)
    (m : SimStE Tx Hash np n Hz PK SK X ×
      Trace (SimStE Tx Hash np n Hz PK SK X) (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np) × Bool)
    (e : EnvEv Tx Hash np Hz X) (hI : MInvE P Sch F x₀ dt Tree K Δ ν d w ε ω m) :
    ∃ p, (monitor (chainSimω P Sch F x₀ dt Tree K Δ ω) (chainFE P Δ ν d w ε).guard).step m e =
        SPComp.pure p ∧ MInvE P Sch F x₀ dt Tree K Δ ν d w ε ω p.1 ∧
      (m.2.2 = true → p.1.2.2 = true) := by
  obtain ⟨s, tr, b⟩ := m
  obtain ⟨hseed, hlen, hj, htr, hb⟩ := hI
  obtain ⟨x, hx, hx1⟩ := chainSimω_step_pure P Sch F x₀ dt Tree K Δ ω s e
  simp only at hseed hlen hj htr hb
  rw [hseed] at hx1
  refine ⟨((x.1, tr ++ [(e, x.2, x.1)],
      b || !(chainFE P Δ ν d w ε).guard (tr ++ [(e, x.2, x.1)])), x.2),
    by simp only [monitor, hx, SPComp.pure_bind], ?_, fun h => by simp only at h; simp [h]⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [hx1, pstNext]
  · simp [hx1, pstNext, hlen]
  · simp only [hx1, pstNext]
    rw [hj, steps_length_append_singleton]
  · intro t ht
    simp only [List.length_append, List.length_singleton] at ht
    rw [FTree.Example.stAt_snoc]
    rcases Nat.lt_or_ge tr.length t with h | h
    · obtain rfl : t = tr.length + 1 := by omega
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      have hk : (s.1.2.1 ++ [e]).take (tr.length + 1) = s.1.2.1 ++ [e] :=
        List.take_of_length_le (by simp [hlen])
      simp only [stViewE, hx1, pstNext, hk]
      rw [hj, steps_length_append_singleton]
    · rw [ite_eq_left h, htr t h, hx1]
      simp only [pstNext]
      rw [List.take_append_of_le_length (by omega)]
  · intro hb'
    refine ⟨by simp, ?_⟩
    cases b
    · simpa using hb'
    · by_contra hg
      have hg' : (chainFE P Δ ν d w ε).guard (tr ++ [(e, x.2, x.1)]) = true := by simpa using hg
      have := fTree_guard_prefix stViewE honestP (slotTree P) (chainP_stable P ν d w ε) _ _
        (List.prefix_append tr [(e, x.2, x.1)]) hg'
      have h2 : (chainFE P Δ ν d w ε).guard tr = true := this
      rw [(hb rfl).2] at h2
      exact Bool.false_ne_true h2

open Classical in
/-- **The flag of the monitor for a fixed seed.** For the seed `ω`, the guard of `chainFE` fails
on the run of `chainSimω ω` with at most the probability that `GoodE` fails for the final log. -/
theorem guardFail_chainSimω_le (hIP : ∀ p : Fin np, CorruptionStatus p = .Honest → p ∈ P.IP)
    (hGB : P.GB.sl = 0) (K Δ : ℕ) (ν : PMF SlotKind) (d w : ℕ) (ε : ℝ)
    (hw4 : K + 1 < d + 2 ∨ 4 ≤ w) (ω : Seed Tx Hash np n Hz PK SK) {ζ : Type}
    (Z : Env (Strat ζ (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) ζ) :
    guardFail (chainSimω P Sch F x₀ dt Tree K Δ ω) (chainFE P Δ ν d w ε).guard Z ≤
      prFinal (chainSimω P Sch F x₀ dt Tree K Δ ω)
        (fun t => decide (¬GoodE P Sch F x₀ dt Tree ν K d w ε ω t.1.2.1)) Z := by
  rw [← prFinal_monitor _ (chainFE P Δ ν d w ε).guard]
  refine prBad_le_prFinal_of_det _ _ _ (MInvE P Sch F x₀ dt Tree K Δ ν d w ε ω)
    (fun m => m.2.2 = true) ?_ (fun m e hI => mInvE_step P Sch F x₀ dt Tree K Δ ν d w ε ω m e hI)
    (fun m _ h => h) ?_ Z
  · refine ⟨rfl, rfl, rfl, fun t ht => ?_, fun h => by simp [monitor] at h⟩
    obtain rfl : t = 0 := Nat.le_zero.1 ht
    rfl
  · rintro ⟨s, tr, b⟩ ⟨hseed, hlen, hj, htr, hb⟩ hb1
    simp only at hb1 hlen htr hb
    obtain ⟨hne, hg⟩ := hb hb1
    simp only [decide_eq_true_eq]
    intro hG
    have := guard_trueE P Sch F x₀ dt Tree K Δ ν d w ε hIP hGB hw4 ω s.1.2.1 hG tr
      (List.length_pos_iff.2 hne) hlen htr
    rw [hg] at this
    exact Bool.false_ne_true this

/-- **Averaging the monitor over the seed.** For an environment that activates the protocol at
least once, the guard of `chainFE` fails on the run of `chainSimE` with the average over the
seed `ω ∼ seedDist` of the probabilities that it fails on the run of `chainSimω ω`. -/
theorem guardFail_chainSimE (K : ℕ) (μ : PMF (Option (Fin np))) (W Δ : ℕ) (ν : PMF SlotKind)
    (d w : ℕ) (ε : ℝ) {ζ : Type}
    (Z : Env (Strat ζ (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) ζ) (hZ : 0 < Z.input.rounds) :
    guardFail (chainSimE P Sch F x₀ dt Tree H cd K μ W Δ) (chainFE P Δ ν d w ε).guard Z =
      ∑' ω, seedDist Sch H cd μ P.h0 W n ω *
        guardFail (chainSimω P Sch F x₀ dt Tree K Δ ω) (chainFE P Δ ν d w ε).guard Z := by
  have hrun := run_bind_firstSample (sampleFrom (ofPMF (seedDist Sch H cd μ P.h0 W n)))
    (monitor (chainSimE P Sch F x₀ dt Tree H cd K μ W Δ) (chainFE P Δ ν d w ε).guard)
    (fun ω => monitor (chainSimω P Sch F x₀ dt Tree K Δ ω) (chainFE P Δ ν d w ε).guard)
    (fun m => m.1.1.1.isNone) exploded (sampleFrom_isPure _) (fun _ => rfl) (fun e => ?_)
    (fun ω t e ht => ?_) (fun ω t e => ?_) Z.input hZ
  · unfold guardFail prBad
    rw [hrun, SPComp.bind_assoc, prTrue_bind_sampleFrom]
    refine tsum_congr fun ω => ?_
    rw [ofPMF_apply_some]
  · simp only [monitor, chainSimE, chainSimω, Hybrid.withSub, chainHybridE, seedOf,
      SPComp.bind_assoc, SPComp.pure_bind]
  · obtain ⟨⟨⟨o, r⟩, q⟩, tr, b⟩ := t
    cases o with
    | none => simp at ht
    | some ω' => rfl
  · obtain ⟨x, hx, hx1⟩ := chainSimω_step_pure P Sch F x₀ dt Tree K Δ ω t.1 e
    simp only [monitor, hx, SPComp.pure_bind]
    simp [goodK, hx1, pstNext]

open Classical in
/-- **Guard failure is bounded by the failure bound against the environment.** For every
environment `Z`, the guard of `chainFE` fails on the run of `chainSimE` with probability at most
`posFailE … Z`, under the hypotheses of `pos_nsb_securityE`, when moreover the genesis block has
slot `0` and `4 ≤ w` unless `K + 1 < d + 2`. -/
theorem guardFailE_le (hP : ProtocolHyp P) (hTree : Tree.Longest)
    (μ : PMF (Option (Fin np))) (W K Δ d w : ℕ) (ε : ℝ)
    (hwd : w ≤ d) (hWn : W + d ≤ n) (hn : K + 2 ≤ n) (hHz : K + 1 ≤ Hz)
    (hε : 0 ≤ ε) (hγ : 2 * pA (kindLaw μ) ≤ pH (kindLaw μ))
    (hw : (w : ℝ) ≤ d * (pH (kindLaw μ) - pA (kindLaw μ)))
    (h3 : (3 : ℝ) ≤ d * (pH (kindLaw μ) - 2 * pA (kindLaw μ)))
    (hGB : P.GB.sl = 0) (hw4 : K + 1 < d + 2 ∨ 4 ≤ w) {ζ : Type}
    (Z : Env (Strat ζ (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) ζ) :
    guardFail (chainSimE P Sch F x₀ dt Tree H cd K μ W Δ) (chainFE P Δ (kindLaw μ) d w ε).guard Z ≤
      posFailE P Sch F x₀ dt Tree H cd μ W K Δ d w ε Z := by
  rcases Nat.eq_zero_or_pos Z.input.rounds with h0 | hZ
  · have : guardFail (chainSimE P Sch F x₀ dt Tree H cd K μ W Δ)
        (chainFE P Δ (kindLaw μ) d w ε).guard Z = 0 := by
      unfold guardFail prBad run
      rw [h0]
      simp [loop, prTrue_pure, monitor, exploded]
    rw [this]
    exact bot_le
  · rw [guardFail_chainSimE P Sch F x₀ dt Tree H cd K μ W Δ (kindLaw μ) d w ε Z hZ]
    refine le_trans (ENNReal.tsum_le_tsum fun ω => ?_)
      (pos_nsb_securityE P Sch F x₀ dt Tree H cd hP hTree μ W K Δ d w ε hwd hWn hn hHz hε hγ hw h3
        Z)
    gcongr
    exact guardFail_chainSimω_le P Sch F x₀ dt Tree (honest_mem_IP P hP) hGB K Δ (kindLaw μ) d w ε
      hw4 ω Z

/-- **PoS-NSB driven by an environment realizes `F_Tree` in the clock-and-network hybrid
model.** Under the hypotheses of `pos_nsb_securityE`, when moreover the genesis block has slot
`0` (`hGB`) and `4 ≤ w` unless `K + 1 < d + 2` (`hw4`), the protocol driven by the environment
with the reference clock and network (`chainRealE`) realizes the ideal world of `F_Tree^P`
(`chainFE`, with `P = chainP`) with the simulator `chainSimE`: every environment `Z` has
advantage at most `posFailE … Z`, the slot bound plus the collision-resistance advantage of the
explicit collision finder `collFinderE … Z` and the EUF-CMA advantages of the explicit forgers
`forgerE … Z i`. -/
theorem chain_realizesE (hP : ProtocolHyp P) (hTree : Tree.Longest)
    (μ : PMF (Option (Fin np))) (W K d w : ℕ) (ε : ℝ) (Δ : ℕ)
    (hwd : w ≤ d) (hWn : W + d ≤ n) (hn : K + 2 ≤ n) (hHz : K + 1 ≤ Hz)
    (hε : 0 ≤ ε) (hγ : 2 * pA (kindLaw μ) ≤ pH (kindLaw μ))
    (hw : (w : ℝ) ≤ d * (pH (kindLaw μ) - pA (kindLaw μ)))
    (h3 : (3 : ℝ) ≤ d * (pH (kindLaw μ) - 2 * pA (kindLaw μ)))
    (hGB : P.GB.sl = 0 := by rfl)
    (hw4 : K + 1 < d + 2 ∨ 4 ≤ w := by first | exact Or.inr (by norm_num) | exact Or.inl (by omega)) :
    RealizesBound (chainRealE P Sch F x₀ dt Tree H cd K μ W Δ)
      (ideal (chainFE P Δ (kindLaw μ) d w ε) (chainSimE P Sch F x₀ dt Tree H cd K μ W Δ))
      (fun _ Z => posFailE P Sch F x₀ dt Tree H cd μ W K Δ d w ε Z) := by
  refine ⟨fun ζ Z => ?_⟩
  have h := clockNet_hybrid_compose H₁ Δ
    (chainHybridE P Sch F x₀ dt Tree K (sampleFrom (ofPMF (seedDist Sch H cd μ P.h0 W n)))
      (sampleFrom_ofPMF_noFail _))
    (chainSimE P Sch F x₀ dt Tree H cd K μ W Δ) (chainFE P Δ (kindLaw μ) d w ε)
    (Hybrid.withSub_noFail _ _ (Hybrid.ideal_noFail _ _ fun _ _ => SPComp.pure_noFail _)) rfl
    (fun _ _ _ => rfl) ζ Z
  exact h.trans (guardFailE_le P Sch F x₀ dt Tree H cd hP hTree μ W K Δ d w ε hwd hWn hn hHz hε
    hγ hw h3 hGB hw4 Z)

end Guard

end CatCryptCore.Consensus.UC.ChainEnv
