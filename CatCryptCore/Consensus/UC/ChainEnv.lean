/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.UC.Chain
public import CatCryptCore.Consensus.PoSNSB.Prob.Script
public import CatCryptCore.Crypto.UCTransparentAdv
public import CatCryptCore.ForMathlib.PMFUniform

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# PoS-NSB driven by an environment

The protocol of `CatCryptCore.Consensus.UC.Chain` runs the execution of a fixed adversary and
ignores the inputs of the environment. In this file the environment drives the execution: its
inputs are honest transactions `TxIn Tx np` and adversary inputs `AdvIn X`, which run the next
phase with an index `x : X` of a family of adversaries `F : AdvFamily X S` or query the hash
function. The protocol records the inputs in a log; the execution after `j` phase entries is
recomputed from the seed and the log (`CatCryptCore.Consensus.PoSNSB.Prob.Script`): the honest
transactions are `txOf dt log` and the adversary is `F.at (scriptOfD x₀ log)`.

For every environment `Z`, the probability that chain growth, chain quality, common prefix or
the honest tip fails on the execution of the final log of the run of `Z` is at most
`posFailE … Z`: the slot bound, plus the collision-resistance advantage of the explicit collision
finder `collFinderE … Z`, plus the sum over the parties `i` of the EUF-CMA advantages of the
explicit forgers `forgerE … Z i` (`pos_nsb_securityE`). Both reductions run the environment
from its heap. The forger simulates the phases with the challenge key through the equalities of
runs `SimEq` of `CatCryptCore.Consensus.PoSNSB.Prob.Reduction`.

## Main definitions

* `chainHybridE P Sch F x₀ dt Tree K c hc` — the hybrid protocol over the clock and the network
  whose first activation draws the seed from `c`. Its state is an optional seed, the log, the
  number of phase entries of the log, the view of the last phase (reported as phase `min j K`,
  `phaseView`) and the leakage of the last input. Every activation records its input in the log;
  a phase entry runs the next phase and sends the clock request `clockReq` of `Chain`, a hash
  query leaks the hash value, and the output is the clock round, the view and the leakage.
* `chainRealE`, `chainSimE` — the protocol with the reference and the ideal clock and network,
  for seeds drawn from `seedDist Sch H cd μ P.h0 W n`; `chainSimω ω` — the protocol with the
  ideal clock and network for the fixed seed `ω`.
* `GoodE` — the property `Good` of `PoSNSB` for the execution of a log.
* `finalLog`, `collFinderE` — the log at the end of the run of an environment against
  `chainSimω ω`, and the collision finder that runs the environment from its heap on the seed of
  the challenge key and searches for a collision in the execution of the final log.
* `simLoop`, `forgerE` — the forger of an environment: it runs the kernel of the environment
  from its heap against the protocol simulated with the challenge key for party `i`, stops at
  the first forgery of party `i`, and simulates the remaining phases of the final log.
* `posFailE` — the failure bound against an environment.

## Main results

* `callIdx_of_mem_phaseCalls`, `forgeBy_append_iff` — the calls of phase `k` belong to phase
  `k`, so the forgeries of the first `j` phases of a log ignore what is appended to it.
* `simLoop_spec` — the probability of a forgery of party `i` on the final log of the run is at
  most the winning probability of the forger's loop.
* `prob_forgeE_le`, `prob_collisionE_le`, `prob_slotE_le` — the three terms of `posFailE`.
* `pos_nsb_securityE` — the failure probability against an environment is at most `posFailE`;
  `pos_nsb_security_of_env` recovers `pos_nsb_security` at the environment without activations,
  and `forger_eq_env`, `forger_adv_eq_env` identify `forger` with the zero-round `forgerE`.
* `chainSimω_step_pure` — the steps of `chainSimω ω` are deterministic.
* `run_chainSimE` — the run against `chainSimE` is the average over the seed of the runs against
  `chainSimω ω`.
* `phaseView_succ`, `phaseView_succ_of_le` — the view of the next phase extends the trees of the
  view of the current phase by the positions of the next phase, up to phase `K`.
* `collFinder_adv_eq_env` — the collision finder `collFinder` of a fixed adversary `A` has the
  advantage of `collFinderE` for the constant family of `A`, the transaction selection of the
  protocol and an environment without activations.
-/

namespace CatCryptCore.Consensus.PoSNSB

open Parameters BlockParameters Corruption Execution
open CatCrypt.Crypto CatCrypt.Crypto.Signatures CatCrypt.Crypto.Assumptions

/-! ## The phase of an adversary call -/

section CallIdx

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ} {PK SK Sig : Type}
  (Sch : PSigScheme (Block Tx Hash (Fin np)) PK SK Sig) [hS : Sch.Deterministic]

/-- The states at which a fold applies its steps satisfy every invariant of the steps. -/
theorem mem_foldrCalls_inv {α β : Type*} (g : α → β → β) (I : β → Prop)
    (hI : ∀ a b, I b → I (g a b)) (N : β) (hN : I N) :
    ∀ (l : List α), ∀ x ∈ foldrCalls g N l, I x.2 := by
  have hf : ∀ l : List α, I (l.foldr g N) := by
    intro l
    induction l with
    | nil => exact hN
    | cons a l ih => exact hI _ _ ih
  intro l
  induction l with
  | nil => simp [foldrCalls]
  | cons a l ih =>
    intro x hx
    simp only [foldrCalls, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hf l
    · exact ih x hx

/-- **The calls of phase `k` belong to phase `k`.** Every adversary call of phase `k` of the
real execution has the phase `callIdx c = k`. -/
theorem callIdx_of_mem_phaseCalls (P : Protocol Tx Hash np n Hz) (ω : Seed Tx Hash np n Hz PK SK)
    (A : Adversary Tx Hash np n Hz PK Sig) (k : ℕ) :
    ∀ c ∈ phaseCalls Sch P ω A (sTrace Sch P ω A false k), callIdx c = k := by
  let _ := ω.params P; let _ := ω.bparams P
  obtain ⟨hT, hp⟩ := sTrace_clock Sch P ω A false k
  set N := sTrace Sch P ω A false k with hN
  intro c hc
  unfold phaseCalls at hc
  unfold progOf at hp
  by_cases h0 : k % 3 = 0
  · rw [if_pos h0] at hp
    rw [hp] at hc
    obtain ⟨x, hx, hcx⟩ := List.mem_flatMap.1 hc
    have ht : x.2.t_now = N.t_now := mem_foldrCalls_inv _ (fun M => M.t_now = N.t_now)
      (fun p M hM => (sRcv_t_now Sch P ω A false p M).trans hM) N rfl _ x hx
    unfold stepCalls at hcx
    by_cases hh : ((x.2.state_map x.1).isSome && is_corrupt x.1) = true
    · simp only [hh, if_true, Bool.false_eq_true, if_false, List.mem_singleton] at hcx
      subst hcx
      have hf : (fetch_msgs x.1 x.2).2.t_now = x.2.t_now := by
        simp [fetch_msgs, rmv_zero_msgs]
      simp only [callIdx, rcvCall, Option.isSome_some, if_true, hf, ht, hT]
      omega
    · simp [hh] at hcx
  · by_cases h1 : k % 3 = 1
    · rw [if_neg h0, if_pos h1] at hp
      rw [hp] at hc
      obtain ⟨x, hx, hcx⟩ := List.mem_flatMap.1 hc
      have ht : x.2.t_now = N.t_now := mem_foldrCalls_inv _ (fun M => M.t_now = N.t_now)
        (fun p M hM => (sBake_t_now Sch P ω A false p M).trans hM) N rfl _ x hx
      unfold stepCalls at hcx
      by_cases hh : ((x.2.state_map x.1).isSome && is_corrupt x.1) = true
      · simp only [hh, if_true, List.mem_singleton] at hcx
        subst hcx
        simp only [callIdx, bakeCall, Option.isSome_none, Bool.false_eq_true, if_false, ht, hT]
        omega
      · simp [hh] at hcx
    · rw [if_neg h0, if_neg h1] at hp
      rw [hp] at hc
      simp at hc

variable (P : Protocol Tx Hash np n Hz) (ω : Seed Tx Hash np n Hz PK SK)
  {X S : Type} (F : AdvFamily X S Tx Hash np n Hz PK Sig)

/-- **Causality of the forgeries.** For a log with at least `j` phase entries, the forgeries of
party `i` on the adversary calls of the first `j` phases of the execution of an extension of the
log are those of the execution of the log. -/
theorem forgeBy_append_iff (i : Fin np) (x₀ : X) (d : Slot → Fin np → Tx) {j : ℕ}
    {log : List (LogEvOf X Tx Hash np Hz)} (hj : j ≤ (steps log).length)
    (l : List (LogEvOf X Tx Hash np Hz)) :
    (∃ c ∈ traceCalls Sch (P.withTx (txOf d (log ++ l))) ω (F.at (scriptOfD x₀ (log ++ l))) j,
        ForgedBy Sch ω (F.at (scriptOfD x₀ (log ++ l))) i c) ↔
      ∃ c ∈ traceCalls Sch (P.withTx (txOf d log)) ω (F.at (scriptOfD x₀ log)) j,
        ForgedBy Sch ω (F.at (scriptOfD x₀ log)) i c := by
  have hσ : ∀ k < j, scriptOfD x₀ (log ++ l) k = scriptOfD x₀ log k :=
    fun k hk => scriptOfD_append x₀ (by omega) l
  have ht : ∀ sl p, 3 * (sl - 1) + 1 < j → txOf d (log ++ l) sl p = txOf d log sl p :=
    fun sl p hsl => txOf_append d (by omega) l p
  rw [traceCalls_congr_of_agree Sch P ω F j (txOf d (log ++ l)) (txOf d log)
    (scriptOfD x₀ (log ++ l)) (scriptOfD x₀ log) hσ ht]
  refine exists_congr fun c => and_congr_right fun hc => ?_
  have hci : callIdx c < j := by
    unfold traceCalls at hc
    obtain ⟨k, hk, hck⟩ := List.mem_flatMap.1 hc
    rw [callIdx_of_mem_phaseCalls Sch (P.withTx (txOf d log)) ω (F.at (scriptOfD x₀ log)) k c hck]
    exact List.mem_range.1 hk
  unfold ForgedBy
  rw [advRaw_at_congr Sch ω F c (hσ _ hci)]

end CallIdx

end CatCryptCore.Consensus.PoSNSB

namespace CatCryptCore.Consensus.UC.ChainEnv

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent CatCrypt.NonUniform
open CatCryptCore.Consensus.UC.FTree CatCryptCore.Consensus.UC.Chain
open CatCrypt.Crypto.Signatures CatCrypt.Crypto.Assumptions
open PoSNSB Parameters BlockParameters Corruption Execution ClockNet
open scoped ENNReal

/-! ## The views of consecutive phases -/

section Views

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ} {PK SK Sig : Type}
  (P : Protocol Tx Hash np n Hz) (Sch : PSigScheme (Block Tx Hash (Fin np)) PK SK Sig)
  [Sch.Deterministic] (A : Adversary Tx Hash np n Hz PK Sig) (Tree : TreeFamily P)

/-- Before phase `K`, the view of the next phase has the round and the positions of the next
phase, and its trees extend those of the current view by the positions of the next phase. -/
theorem phaseView_succ (K : ℕ) (ω : Seed Tx Hash np n Hz PK SK) {j : ℕ} (hj : j < K) :
    phaseView P Sch A Tree K ω (j + 1) =
      { round := roundAt P Sch A ω (j + 1)
        tree := fun o => (phaseView P Sch A Tree K ω j).tree o ++ posAt P Sch A Tree ω (j + 1) o
        pos := posAt P Sch A Tree ω (j + 1)
        fin := fun _ => [] } := by
  simp only [phaseView, Nat.min_eq_left hj.le, Nat.min_eq_left (Nat.succ_le_of_lt hj),
    List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- From phase `K` on, the view does not change. -/
theorem phaseView_succ_of_le (K : ℕ) (ω : Seed Tx Hash np n Hz PK SK) {j : ℕ} (hj : K ≤ j) :
    phaseView P Sch A Tree K ω (j + 1) = phaseView P Sch A Tree K ω j := by
  simp only [phaseView, Nat.min_eq_right hj, Nat.min_eq_right (Nat.le_succ_of_le hj)]

end Views

/-! ## The protocol driven by an environment -/

section Protocol

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ} {PK SK Sig : Type}
  (P : Protocol Tx Hash np n Hz) (Sch : PSigScheme (Block Tx Hash (Fin np)) PK SK Sig)
  [Sch.Deterministic] {X S : Type} (F : AdvFamily X S Tx Hash np n Hz PK Sig) (x₀ : X)
  (dt : Slot → Fin np → Tx) (Tree : TreeFamily P)
  (H : HashScheme) (cd : H.Codec (BlockDom Tx Hash np Hz) Hash)

variable (Tx Hash np Hz X) in
/-- The inputs of the environment: honest transactions and adversary inputs with indices `X`.
They are the entries of the log. -/
abbrev EnvEv := Event (TxIn Tx np) (AdvIn X Tx Hash np Hz)

variable (Tx Hash np) in
/-- The outputs to the environment: the clock round, the view and the leakage. -/
abbrev EnvOut := ChainOut Tx Hash np × Option Hash

variable (Tx Hash np n Hz PK SK X) in
/-- The states of the protocol: an optional seed, the log, the number of phase entries of the
log, the view of the last phase and the leakage of the last input. -/
abbrev PStE :=
  Option (Seed Tx Hash np n Hz PK SK) × List (LogEvOf X Tx Hash np Hz) × ℕ ×
    TreeView (Option (Fin np)) (Block Tx Hash (Fin np)) × Option Hash

variable (Tx Hash np n Hz PK SK X) in
/-- The states of the protocol with the ideal clock and network. -/
abbrev SimStE := PStE Tx Hash np n Hz PK SK X ×
  (CNSt Unit Unit × Trace (CNSt Unit Unit) (CNEv Unit Unit) (CNOut Unit Unit) × Bool)

/-- The view after `j` phases of the execution of the seed `ω` and the log `log`, reported as
phase `min j K`. -/
def viewE (K : ℕ) (ω : Seed Tx Hash np n Hz PK SK) (log : List (LogEvOf X Tx Hash np Hz))
    (j : ℕ) : TreeView (Option (Fin np)) (Block Tx Hash (Fin np)) :=
  phaseView (P.withTx (txOf dt log)) Sch (F.at (scriptOfD x₀ log)) Tree K ω j

/-- The number of phase entries after an input: one more after a phase entry. -/
def phaseNext (j : ℕ) : EnvEv Tx Hash np Hz X → ℕ
  | .inr (.step _) => j + 1
  | _ => j

/-- The leakage of an input under the seed `ω`: the hash value of a hash query. -/
def leakOf (ω : Seed Tx Hash np n Hz PK SK) : EnvEv Tx Hash np Hz X → Option Hash
  | .inr (.hash d) => some (ω.f d)
  | _ => none

/-- The state after the input `e` under the seed `ω`: the input is appended to the log, and the
view and the leakage are those of the extended log. -/
def pstNext (K : ℕ) (ω : Seed Tx Hash np n Hz PK SK) (s : PStE Tx Hash np n Hz PK SK X)
    (e : EnvEv Tx Hash np Hz X) : PStE Tx Hash np n Hz PK SK X :=
  (some ω, s.2.1 ++ [e], phaseNext s.2.2.1 e,
    viewE P Sch F x₀ dt Tree K ω (s.2.1 ++ [e]) (phaseNext s.2.2.1 e), leakOf ω e)

/-- The clock request of the input `e` under the seed `ω`: a phase entry, which runs phase
`j + 1`, sends the request `clockReq` of phase `j` of the extended log; the other inputs read the
clock. -/
def reqOf (ω : Seed Tx Hash np n Hz PK SK) (s : PStE Tx Hash np n Hz PK SK X) :
    EnvEv Tx Hash np Hz X → CNEv Unit Unit
  | .inr (.step x) => clockReq (P.withTx (txOf dt (s.2.1 ++ [.inr (.step x)]))) Sch
      (F.at (scriptOfD x₀ (s.2.1 ++ [.inr (.step x)]))) ω s.2.2.1
  | _ => .inl ((), .read)

/-- The seed of a state: the seed drawn from `c` for a state without seed. -/
noncomputable def seedOf (c : SPComp (Seed Tx Hash np n Hz PK SK))
    (s : PStE Tx Hash np n Hz PK SK X) : SPComp (Seed Tx Hash np n Hz PK SK) :=
  match s.1 with
  | none => c
  | some ω => SPComp.pure ω

theorem seedOf_noFail (c : SPComp (Seed Tx Hash np n Hz PK SK)) (hc : SPComp.NoFail c)
    (s : PStE Tx Hash np n Hz PK SK X) : SPComp.NoFail (seedOf c s) := by
  rcases s with ⟨_ | ω, r⟩
  · exact hc
  · exact SPComp.pure_noFail _

/-- **The PoS-NSB protocol driven by an environment**, as a hybrid protocol over the clock and
the network. The first activation draws the seed from `c`; every activation appends its input
to the log, stores the state `pstNext` and sends the clock request `reqOf`. The output is the
clock round, the stored view and the stored leakage. -/
noncomputable def chainHybridE (K : ℕ) (c : SPComp (Seed Tx Hash np n Hz PK SK))
    (hc : SPComp.NoFail c) :
    Hybrid (PStE Tx Hash np n Hz PK SK X) (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)
      (CNEv Unit Unit) (CNOut Unit Unit) where
  init := (none, [], 0, startView P, none)
  pre s e := SPComp.bind (seedOf c s) fun ω =>
    SPComp.pure (pstNext P Sch F x₀ dt Tree K ω s e, reqOf P Sch F x₀ dt ω s e)
  post s o := SPComp.pure (s, ((o.1, s.2.2.2.1), s.2.2.2.2))
  pre_noFail s _ :=
    Assumptions.SPComp.bind_noFail (seedOf_noFail c hc s) fun _ => SPComp.pure_noFail _
  post_noFail _ _ := SPComp.pure_noFail _

/-- The real world: the protocol driven by the environment, with seeds drawn from `seedDist`,
and the reference clock and network. -/
noncomputable def chainRealE (K : ℕ) (μ : PMF (Option (Fin np))) (W Δ : ℕ) :=
  (chainHybridE P Sch F x₀ dt Tree K (sampleFrom (ofPMF (seedDist Sch H cd μ P.h0 W n)))
    (sampleFrom_ofPMF_noFail _)).withSub (clockNet (M := Unit) H₁ Δ).proto

/-- The protocol driven by the environment, with seeds drawn from `seedDist`, and the ideal
clock and network. -/
noncomputable def chainSimE (K : ℕ) (μ : PMF (Option (Fin np))) (W Δ : ℕ) :=
  (chainHybridE P Sch F x₀ dt Tree K (sampleFrom (ofPMF (seedDist Sch H cd μ P.h0 W n)))
    (sampleFrom_ofPMF_noFail _)).withSub (ideal (clockNetF (M := Unit) H₁ Δ) (clockNet H₁ Δ).proto)

/-- The protocol driven by the environment for the fixed seed `ω`, with the ideal clock and
network. -/
noncomputable def chainSimω (K Δ : ℕ) (ω : Seed Tx Hash np n Hz PK SK) :=
  (chainHybridE P Sch F x₀ dt Tree K (SPComp.pure ω) (SPComp.pure_noFail _)).withSub
    (ideal (clockNetF (M := Unit) H₁ Δ) (clockNet H₁ Δ).proto)

instance (K : ℕ) (μ : PMF (Option (Fin np))) (W Δ : ℕ) :
    Lossless (chainRealE P Sch F x₀ dt Tree H cd K μ W Δ) :=
  Hybrid.lossless_withSub _ _

instance (K : ℕ) (μ : PMF (Option (Fin np))) (W Δ : ℕ) :
    Lossless (chainSimE P Sch F x₀ dt Tree H cd K μ W Δ) :=
  ⟨Hybrid.withSub_noFail _ _ (Hybrid.ideal_noFail _ _ fun _ _ => SPComp.pure_noFail _)⟩

instance (K Δ : ℕ) (ω : Seed Tx Hash np n Hz PK SK) :
    Lossless (chainSimω P Sch F x₀ dt Tree K Δ ω) :=
  ⟨Hybrid.withSub_noFail _ _ (Hybrid.ideal_noFail _ _ fun _ _ => SPComp.pure_noFail _)⟩

/-- **The steps for a fixed seed are deterministic.** A step of `chainSimω ω` returns a single
state, whose protocol component is `pstNext` for the seed of the state, or `ω` for a state
without seed. -/
theorem chainSimω_step_pure (K Δ : ℕ) (ω : Seed Tx Hash np n Hz PK SK)
    (s : SimStE Tx Hash np n Hz PK SK X) (e : EnvEv Tx Hash np Hz X) :
    ∃ x, (chainSimω P Sch F x₀ dt Tree K Δ ω).step s e = SPComp.pure x ∧
      x.1.1 = pstNext P Sch F x₀ dt Tree K (s.1.1.getD ω) s.1 e := by
  obtain ⟨⟨o, r⟩, q⟩ := s
  cases o <;>
  · simp only [chainSimω, Hybrid.withSub, chainHybridE, seedOf, ideal, DetFunc.proto,
      SPComp.pure_bind]
    exact ⟨_, rfl, rfl⟩

/-- **Averaging over the seed.** For an environment that activates the protocol at least once,
the run against `chainSimE` is the average over the seed `ω ∼ seedDist` of the runs against
`chainSimω ω`. -/
theorem run_chainSimE (K : ℕ) (μ : PMF (Option (Fin np))) (W Δ : ℕ)
    (bad : SimStE Tx Hash np n Hz PK SK X → Bool) {ζ : Type}
    (Z : Strat ζ (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) (hZ : 0 < Z.rounds) :
    run (chainSimE P Sch F x₀ dt Tree H cd K μ W Δ) bad Z =
      SPComp.bind (sampleFrom (ofPMF (seedDist Sch H cd μ P.h0 W n))) fun ω =>
        run (chainSimω P Sch F x₀ dt Tree K Δ ω) bad Z := by
  refine run_bind_firstSample _ (chainSimE P Sch F x₀ dt Tree H cd K μ W Δ)
    (chainSimω P Sch F x₀ dt Tree K Δ) (fun t => t.1.1.isNone) bad (sampleFrom_isPure _)
    (fun _ => rfl) (fun e => ?_) (fun ω t e ht => ?_) (fun ω t e => ?_) Z hZ
  · simp only [chainSimE, chainSimω, Hybrid.withSub, chainHybridE, seedOf, SPComp.bind_assoc,
      SPComp.pure_bind]
  · obtain ⟨⟨o, r⟩, q⟩ := t
    cases o with
    | none => simp at ht
    | some ω' => rfl
  · obtain ⟨x, hx, hx1⟩ := chainSimω_step_pure P Sch F x₀ dt Tree K Δ ω t e
    rw [hx, SPComp.pure_bind]
    simp [goodK, hx1, pstNext]

/-- The property `Good` of `PoSNSB` for the execution of the seed `ω` and the log `log`: the
honest transactions of the log and the family along the indices of the log, with the default
index `x₀` for the phases after the last phase entry. -/
def GoodE (ν : PMF SlotKind) (K d w : ℕ) (ε : ℝ) (ω : Seed Tx Hash np n Hz PK SK)
    (log : List (LogEvOf X Tx Hash np Hz)) : Prop :=
  Good (P.withTx (txOf dt log)) Sch (F.at (scriptOfD x₀ log)) Tree ν K d w ε ω

/-! ## The collision finder of an environment -/

/-- The log at the end of the run of the environment `Z` against `chainSimω ω`. -/
noncomputable def finalLog (K Δ : ℕ) (ω : Seed Tx Hash np n Hz PK SK) {ζ : Type}
    (Z : Strat ζ (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) :
    SPComp (List (LogEvOf X Tx Hash np Hz)) :=
  SPComp.map (fun c => c.2.1.1.2.1) (run (chainSimω P Sch F x₀ dt Tree K Δ ω) (fun _ => false) Z)

/-- **The collision finder of an environment.** Under the key `k`, with coins `c` from
`collCoins`, it runs the environment `Z` from its heap against `chainSimω` for the seed
`⟨c.1, cd.hashOn k, c.2⟩`, and outputs `collFind` for the execution of the final log. -/
noncomputable def collFinderE (μ : PMF (Option (Fin np))) (W K Δ : ℕ) {ζ : Type}
    (Z : Env (Strat ζ (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) ζ) : CR_Search_Adversary H :=
  collFinderG Sch P H cd μ W K
    (fun ω => SPComp.atHeap Z.heap (finalLog P Sch F x₀ dt Tree K Δ ω Z.input)) (txOf dt)
    (fun log => F.at (scriptOfD x₀ log))

/-- Without activations the final log is empty. -/
theorem finalLog_of_rounds_eq_zero (K Δ : ℕ) (ω : Seed Tx Hash np n Hz PK SK) {ζ : Type}
    (Z : Strat ζ (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) (hZ : Z.rounds = 0) :
    finalLog P Sch F x₀ dt Tree K Δ ω Z = SPComp.pure [] := by
  unfold finalLog run
  rw [hZ]
  simp only [loop, SPComp.map, SPComp.pure_bind]
  rfl

/-- **The fixed-adversary finder is the zero-round instance.** The collision finder
`collFinder Sch P A H cd μ W K` of the adversary `A` has the advantage of the collision finder
`collFinderE` of an environment without activations, for the constant family of `A` and the
transaction selection `P.txSel`. -/
theorem collFinder_adv_eq_env (A : Adversary Tx Hash np n Hz PK Sig) (μ : PMF (Option (Fin np)))
    (W K Δ : ℕ) {ζ : Type}
    (Z : Env (Strat ζ (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) ζ) (hZ : Z.input.rounds = 0) :
    CR_Search_Advantage H (collFinder Sch P A H cd μ W K) =
      CR_Search_Advantage H
        (collFinderE P Sch (AdvFamily.const A) x₀ P.txSel Tree H cd μ W K Δ Z) := by
  unfold collFinderE collFinderG
  simp only [finalLog_of_rounds_eq_zero P Sch (AdvFamily.const A) x₀ P.txSel Tree K Δ _ Z.input hZ]
  unfold CR_Search_Advantage CR_Search_Game collFinder CR_Search_Adversary.ofCoins
  rw [show SPComp.sample H.Key = sampleFrom (ofPMF (PMF.uniformOfFintype H.Key)) from rfl]
  simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, Function.comp_apply, SPComp.pure_bind]
  rw [prTrue_bind_sampleFrom, prTrue_bind_sampleFrom]
  refine tsum_congr fun k => ?_
  congr 1
  rw [prTrue_bind_sampleFrom, prTrue_bind_sampleFrom]
  refine tsum_congr fun c => ?_
  congr 1
  rw [prTrue_bind_atHeap, SPComp.pure_bind]
  simp only [ForkingLemma.prTrue_pure_bool]
  rfl

/-! ## The steps of the ideal clock and network -/

/-- The states of the ideal clock and network. -/
abbrev CNS := CNSt Unit Unit × Trace (CNSt Unit Unit) (CNEv Unit Unit) (CNOut Unit Unit) × Bool

theorem cnStep_pure (Δ : ℕ) (q : CNS) (r : CNEv Unit Unit) :
    ∃ y, (ideal (clockNetF (M := Unit) H₁ Δ) (clockNet H₁ Δ).proto).step q r = SPComp.pure y := by
  simp only [ideal, DetFunc.proto, SPComp.pure_bind]
  exact ⟨_, rfl⟩

/-- The next state and the output of the ideal clock and network on the request `r`. -/
noncomputable def cnNext (Δ : ℕ) (q : CNS) (r : CNEv Unit Unit) : CNS × CNOut Unit Unit :=
  Classical.choose (cnStep_pure Δ q r)

theorem cnStep_eq (Δ : ℕ) (q : CNS) (r : CNEv Unit Unit) :
    (ideal (clockNetF (M := Unit) H₁ Δ) (clockNet H₁ Δ).proto).step q r =
      SPComp.pure (cnNext Δ q r) :=
  Classical.choose_spec (cnStep_pure Δ q r)

/-- The clock request of the input `e` after `j` phase entries: a phase entry signals the end of
the round after a baking phase (`progOf`); the other inputs read the clock. -/
def reqJ (j : ℕ) : EnvEv Tx Hash np Hz X → CNEv Unit Unit
  | .inr (.step _) => if progOf j = .Baked then .inl ((), .signal) else .inl ((), .read)
  | _ => .inl ((), .read)

/-- The clock request depends only on the number of phase entries. -/
theorem reqOf_eq (ω : Seed Tx Hash np n Hz PK SK) (s : PStE Tx Hash np n Hz PK SK X)
    (e : EnvEv Tx Hash np Hz X) : reqOf P Sch F x₀ dt ω s e = reqJ s.2.2.1 e := by
  rcases e with e | (x | d)
  · rfl
  · simp only [reqOf, reqJ, clockReq, (sTrace_clock Sch _ ω _ false s.2.2.1).2]
  · rfl

/-- **The step for a fixed seed.** A step of `chainSimω ω` stores `pstNext` for the seed of the
state (`ω` for a state without seed) and the next state of the clock and network on the request
`reqJ`, and outputs the clock round, the view and the leakage of the new state. -/
theorem chainSimω_step_eq (K Δ : ℕ) (ω : Seed Tx Hash np n Hz PK SK)
    (s : SimStE Tx Hash np n Hz PK SK X) (e : EnvEv Tx Hash np Hz X) :
    (chainSimω P Sch F x₀ dt Tree K Δ ω).step s e = SPComp.pure
      ((pstNext P Sch F x₀ dt Tree K (s.1.1.getD ω) s.1 e,
          (cnNext Δ s.2 (reqJ s.1.2.2.1 e)).1),
        (((cnNext Δ s.2 (reqJ s.1.2.2.1 e)).2.1,
            (pstNext P Sch F x₀ dt Tree K (s.1.1.getD ω) s.1 e).2.2.2.1),
          (pstNext P Sch F x₀ dt Tree K (s.1.1.getD ω) s.1 e).2.2.2.2)) := by
  obtain ⟨⟨o, r⟩, q⟩ := s
  cases o <;>
  · simp only [chainSimω, Hybrid.withSub, chainHybridE, seedOf, SPComp.pure_bind, reqOf_eq,
      cnStep_eq, Option.getD_none, Option.getD_some]

/-- The leakage of a seed does not involve the key pairs. -/
theorem leakOf_withKey (ω : Seed Tx Hash np n Hz PK SK) (i : Fin np) (kp : PK × SK)
    (e : EnvEv Tx Hash np Hz X) : leakOf (ω.withKey i kp) e = leakOf ω e := by
  rcases e with e | (x | d) <;> rfl

/-! ## The views computed from the states -/

/-- The positions at a state of the execution of the seed `ω`: the chain the local tree of party
`p` selects at the previous slot, and for the observer `none` the honest tree chain. -/
def posOf (ω : Seed Tx Hash np n Hz PK SK)
    (N : @GlobalState Tx Hash (Fin np) S (ω.params P) (ω.bparams P)) :
    Option (Fin np) → List (Block Tx Hash (Fin np))
  | none => letI := ω.params P; letI := ω.bparams P; honest_tree_chain (Tree ω.L ω.f) N
  | some p => letI := ω.params P; letI := ω.bparams P
      (N.state_map p).elim [] fun l => l.tT.bestChain (N.t_now - 1) l.tree

/-- The view after a phase that reaches the state `N`, from the view `v` of the previous phase:
the slot of `N`, the trees of `v` extended by the positions at `N`, and the positions at `N`. -/
def vNext (ω : Seed Tx Hash np n Hz PK SK) (v : TreeView (Option (Fin np)) (Block Tx Hash (Fin np)))
    (N : @GlobalState Tx Hash (Fin np) S (ω.params P) (ω.bparams P)) :
    TreeView (Option (Fin np)) (Block Tx Hash (Fin np)) where
  round := letI := ω.params P; letI := ω.bparams P; N.t_now
  tree o := v.tree o ++ posOf P Tree ω N o
  pos := posOf P Tree ω N
  fin _ := []

/-- The view `vNext` does not involve the key pairs of the seed. -/
theorem vNext_withKey (ω : Seed Tx Hash np n Hz PK SK) (i : Fin np) (kp : PK × SK)
    (v : TreeView (Option (Fin np)) (Block Tx Hash (Fin np)))
    (N : @GlobalState Tx Hash (Fin np) S (ω.params P) (ω.bparams P)) :
    vNext P Tree (ω.withKey i kp) v N = vNext P Tree ω v N := rfl

theorem posAt_eq_posOf (t : Slot → Fin np → Tx) (σ : ℕ → X) (ω : Seed Tx Hash np n Hz PK SK)
    (j : ℕ) (o : Option (Fin np)) :
    posAt (P.withTx t) Sch (F.at σ) Tree ω j o =
      posOf P Tree ω (sTrace Sch (P.withTx t) ω (F.at σ) false j) o := by
  cases o <;> rfl

/-- The view after `j` phases of a log with at least `j` phase entries ignores what is appended
to the log. -/
theorem viewE_append (K : ℕ) (ω : Seed Tx Hash np n Hz PK SK) {j : ℕ}
    {log : List (LogEvOf X Tx Hash np Hz)} (hj : j ≤ (steps log).length)
    (l : List (LogEvOf X Tx Hash np Hz)) :
    viewE P Sch F x₀ dt Tree K ω (log ++ l) j = viewE P Sch F x₀ dt Tree K ω log j := by
  have h := sTrace_append_of_le Sch P ω F false x₀ dt hj l
  have hp : ∀ k ≤ j, ∀ o, posAt (P.withTx (txOf dt (log ++ l))) Sch
      (F.at (scriptOfD x₀ (log ++ l))) Tree ω k o =
        posAt (P.withTx (txOf dt log)) Sch (F.at (scriptOfD x₀ log)) Tree ω k o := by
    intro k hk o
    rw [posAt_eq_posOf, posAt_eq_posOf, h k hk]
  unfold viewE phaseView
  congr 1
  · unfold roundAt
    rw [h _ (min_le_left _ _)]
  · funext o
    exact List.flatMap_congr fun k hk => hp k (by have := List.mem_range.1 hk; omega) o
  · funext o
    exact hp _ (min_le_left _ _) o

/-- Before phase `K`, the view of the next phase of an extended log is `vNext` of the view of the
log and the state of the next phase. -/
theorem viewE_succ (K : ℕ) (ω : Seed Tx Hash np n Hz PK SK) {j : ℕ} (hjK : j < K)
    {log : List (LogEvOf X Tx Hash np Hz)} (hj : j ≤ (steps log).length)
    (l : List (LogEvOf X Tx Hash np Hz)) :
    viewE P Sch F x₀ dt Tree K ω (log ++ l) (j + 1) =
      vNext P Tree ω (viewE P Sch F x₀ dt Tree K ω log j)
        (sTrace Sch (P.withTx (txOf dt (log ++ l))) ω (F.at (scriptOfD x₀ (log ++ l))) false
          (j + 1)) := by
  rw [← viewE_append P Sch F x₀ dt Tree K ω hj l]
  unfold viewE
  rw [phaseView_succ (P.withTx (txOf dt (log ++ l))) Sch (F.at (scriptOfD x₀ (log ++ l))) Tree K
    ω hjK]
  rfl

/-- From phase `K` on, the view of an extended log does not change. -/
theorem viewE_succ_of_le (K : ℕ) (ω : Seed Tx Hash np n Hz PK SK) {j : ℕ} (hKj : K ≤ j)
    {log : List (LogEvOf X Tx Hash np Hz)} (hj : j ≤ (steps log).length)
    (l : List (LogEvOf X Tx Hash np Hz)) :
    viewE P Sch F x₀ dt Tree K ω (log ++ l) (j + 1) = viewE P Sch F x₀ dt Tree K ω log j := by
  rw [← viewE_append P Sch F x₀ dt Tree K ω hj l]
  unfold viewE
  rw [phaseView_succ_of_le (P.withTx (txOf dt (log ++ l))) Sch (F.at (scriptOfD x₀ (log ++ l)))
    Tree K ω hKj]

/-- The view of the initial phase is `vNext` of the empty view and the initial state. -/
theorem viewE_zero (K : ℕ) (ω : Seed Tx Hash np n Hz PK SK)
    (log : List (LogEvOf X Tx Hash np Hz)) :
    viewE P Sch F x₀ dt Tree K ω log 0 =
      vNext P Tree ω initView
        (sTrace Sch (P.withTx (txOf dt log)) ω (F.at (scriptOfD x₀ log)) false 0) := by
  unfold viewE phaseView vNext
  simp only [Nat.zero_min, zero_add, List.range_one, List.flatMap_singleton, posAt_eq_posOf]
  rfl

/-! ## The forger of an environment -/

/-- The losing output of a forger: query the genesis block and output it with its signature. -/
def loseProg : FProg Tx Hash np Sig := .query P.GB fun σ => .ret (P.GB, σ)

/-- The forger's simulation of the input `e` after the log `log` with `j` phase entries, the
view `v` and the state `N`, continued by `k` on the next view and state: a phase entry before
phase `K` simulates the next phase of the extended log with key `pk` for party `i` and stops with
the first forgery of party `i`; the other inputs keep the view and the state. -/
def simEv (K : ℕ) (i : Fin np) (pk : PK) (ω : Seed Tx Hash np n Hz PK SK)
    (log : List (LogEvOf X Tx Hash np Hz)) (j : ℕ)
    (v : TreeView (Option (Fin np)) (Block Tx Hash (Fin np)))
    (N : @GlobalState Tx Hash (Fin np) S (ω.params P) (ω.bparams P)) (e : EnvEv Tx Hash np Hz X)
    (k : TreeView (Option (Fin np)) (Block Tx Hash (Fin np)) →
      @GlobalState Tx Hash (Fin np) S (ω.params P) (ω.bparams P) → FProg Tx Hash np Sig) :
    FProg Tx Hash np Sig :=
  match e with
  | .inr (.step x) =>
    if j < K then
      simPhase Sch (P.withTx (txOf dt (log ++ [.inr (.step x)])))
        (F.at (scriptOfD x₀ (log ++ [.inr (.step x)]))) i pk ω N fun N' => k (vNext P Tree ω v N') N'
    else k v N
  | _ => k v N

theorem phaseNext_of_stepOf_none (j : ℕ) (e : EnvEv Tx Hash np Hz X) (he : stepOf e = none) :
    phaseNext j e = j := by
  rcases e with e | (x | d)
  · rfl
  · simp [stepOf] at he
  · rfl

/-- An input that is not a phase entry keeps the view and the state. -/
theorem simEv_of_stepOf_none {K : ℕ} {i : Fin np} {pk : PK} {ω : Seed Tx Hash np n Hz PK SK}
    {log : List (LogEvOf X Tx Hash np Hz)} {j : ℕ}
    {v : TreeView (Option (Fin np)) (Block Tx Hash (Fin np))}
    {N : @GlobalState Tx Hash (Fin np) S (ω.params P) (ω.bparams P)} (e : EnvEv Tx Hash np Hz X)
    {k : TreeView (Option (Fin np)) (Block Tx Hash (Fin np)) →
      @GlobalState Tx Hash (Fin np) S (ω.params P) (ω.bparams P) → FProg Tx Hash np Sig}
    (he : stepOf e = none) : simEv P Sch F x₀ dt Tree K i pk ω log j v N e k = k v N := by
  rcases e with e | (x | d)
  · rfl
  · simp [stepOf] at he
  · rfl

/-- **The forger's loop.** With `m` activations left, from the state `z` of the kernel of the
environment `Z` at the heap `h`, the log `log` with `j` phase entries, the view `v`, the state `q`
of the clock and network and the simulated state `N`: draw the next input `e` of `Z`, simulate it
(`simEv`), give `Z` the output of the protocol, and continue. After the last activation it
simulates the remaining phases up to `K` of the final log and loses unless it found a forgery. -/
noncomputable def simLoop (K Δ : ℕ) (i : Fin np) (pk : PK) (ω : Seed Tx Hash np n Hz PK SK)
    {ζ : Type} (Z : Strat ζ (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) :
    ℕ → ζ → Heap → List (LogEvOf X Tx Hash np Hz) → ℕ →
      TreeView (Option (Fin np)) (Block Tx Hash (Fin np)) → CNS →
      @GlobalState Tx Hash (Fin np) S (ω.params P) (ω.bparams P) → FProg Tx Hash np Sig
  | 0, _, _, log, j, _, _, N =>
    simTraceFrom Sch (P.withTx (txOf dt log)) (F.at (scriptOfD x₀ log)) i pk ω (K - j) N
      fun _ => loseProg P
  | m + 1, z, h, log, j, v, q, N =>
    .rand (Z.next z h) fun o => match o with
      | none => loseProg P
      | some ((z₁, e), h₁) =>
        simEv P Sch F x₀ dt Tree K i pk ω log j v N e fun v' N' =>
          .rand (Z.obs z₁ (((cnNext Δ q (reqJ j e)).2.1, v'), leakOf ω e) h₁) fun o' =>
            match o' with
            | none => loseProg P
            | some (z₂, h₂) =>
              simLoop K Δ i pk ω Z m z₂ h₂ (log ++ [e]) (phaseNext j e) v'
                (cnNext Δ q (reqJ j e)).1 N'

/-- **The forger of an environment.** The EUF-CMA adversary obtained from the environment `Z`
and the party `i`: on the verification key `pk` it draws a seed from `seedDist Sch H cd` and runs
the kernel of `Z` from its heap against the protocol simulated with key `pk` for party `i`
(`simLoop`), and outputs the first forgery of party `i`. -/
noncomputable def forgerE (μ : PMF (Option (Fin np))) (W K Δ : ℕ) {ζ : Type}
    (Z : Env (Strat ζ (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) ζ) (i : Fin np) (pk : PK) :
    FProg Tx Hash np Sig :=
  .rand (seedDist Sch H cd μ P.h0 W n) fun ω =>
    simLoop P Sch F x₀ dt Tree K Δ i pk ω Z.input Z.input.rounds Z.input.init Z.heap [] 0
      (vNext P Tree ω initView (sTrace Sch (P.withTx (txOf dt ([] : List (LogEvOf X Tx Hash np Hz))))
        ω (F.at (scriptOfD x₀ ([] : List (LogEvOf X Tx Hash np Hz)))) false 0))
      (ideal (clockNetF (M := Unit) H₁ Δ) (clockNet H₁ Δ).proto).init
      (sTrace Sch (P.withTx (txOf dt ([] : List (LogEvOf X Tx Hash np Hz)))) ω
        (F.at (scriptOfD x₀ ([] : List (LogEvOf X Tx Hash np Hz)))) false 0)

/-! ## The forger simulates the run of the environment -/

/-- A bind after `c` accepts from the heap `h` with at most the probability that an oracle
adversary that samples from `c h` produces an accepted output, when every continuation of the
bind is dominated by the corresponding continuation of the adversary. -/
theorem prTrue_bind_le_run_rand {α D R β σO : Type} (c : SPComp α) (Kr : α → SPComp Bool)
    (h : Heap) (O : σO → D → PMF (R × σO)) (kont : Option (α × Heap) → OracleAdv D R β)
    (l : σO) (w : β × σO → Bool)
    (hk : ∀ a h', prTrue (Kr a) h' ≤ ((OracleAdv.run O (kont (some (a, h'))) l).map w) true) :
    prTrue (SPComp.bind c Kr) h ≤ ((OracleAdv.run O (.rand (c h) kont) l).map w) true := by
  rw [prTrue_bind_eq_weighted, OracleAdv.run_rand, PMF.map_bind, PMF.bind_apply]
  refine ENNReal.tsum_le_tsum fun o => ?_
  rcases o with _ | ⟨a, h'⟩
  · simp
  · gcongr
    exact hk a h'

/-- The invariant of the forger along a run against `chainSimω ω`: the log has `j` phase
entries, `v` is the view of the log after `j` phases, `N` is the state of its execution after
`min j K` phases, the blocks of the signing queries `l` lie in the history of `N`, and no
adversary call of these phases forges a block of party `i`. -/
def SimInv (K : ℕ) (i : Fin np) (ω : Seed Tx Hash np n Hz PK SK)
    (log : List (LogEvOf X Tx Hash np Hz)) (j : ℕ)
    (v : TreeView (Option (Fin np)) (Block Tx Hash (Fin np)))
    (N : @GlobalState Tx Hash (Fin np) S (ω.params P) (ω.bparams P))
    (l : List (Block Tx Hash (Fin np) × Sig)) : Prop :=
  j = (steps log).length ∧ v = viewE P Sch F x₀ dt Tree K ω log j ∧
    N = sTrace Sch (P.withTx (txOf dt log)) ω (F.at (scriptOfD x₀ log)) false (min j K) ∧
    (∀ b ∈ l.map Prod.fst, b ∈ hb (P.withTx (txOf dt log)) (F.at (scriptOfD x₀ log)) (ω := ω) N) ∧
    ¬∃ c ∈ traceCalls Sch (P.withTx (txOf dt log)) ω (F.at (scriptOfD x₀ log)) (min j K),
      ForgedBy Sch ω (F.at (scriptOfD x₀ log)) i c

open Classical in
/-- The forging event of party `i` on the final log of a state: an adversary call of the first
`K` phases of the execution of the log forges a block of party `i`. -/
noncomputable def forgeEv (K : ℕ) (i : Fin np) (ω : Seed Tx Hash np n Hz PK SK)
    (t : SimStE Tx Hash np n Hz PK SK X) : Bool :=
  decide (ForgeBy Sch (P.withTx (txOf dt t.1.2.1)) ω (F.at (scriptOfD x₀ t.1.2.1)) K i)

/-- The non-step inputs keep the invariant on the extended log. -/
theorem simInv_append (K : ℕ) (i : Fin np) (ω : Seed Tx Hash np n Hz PK SK)
    {log : List (LogEvOf X Tx Hash np Hz)} {j : ℕ}
    {v : TreeView (Option (Fin np)) (Block Tx Hash (Fin np))}
    {N : @GlobalState Tx Hash (Fin np) S (ω.params P) (ω.bparams P)}
    {l : List (Block Tx Hash (Fin np) × Sig)} (hI : SimInv P Sch F x₀ dt Tree K i ω log j v N l)
    (e : EnvEv Tx Hash np Hz X) (he : stepOf e = none) :
    SimInv P Sch F x₀ dt Tree K i ω (log ++ [e]) j v N l := by
  obtain ⟨hjl, hv, hN, hl, hnf⟩ := hI
  have hmj : min j K ≤ (steps log).length := by omega
  refine ⟨?_, ?_, ?_, hl, ?_⟩
  · simp [hjl, steps, he]
  · rw [hv, viewE_append P Sch F x₀ dt Tree K ω hjl.le]
  · rw [hN, sTrace_append_of_le Sch P ω F false x₀ dt hmj [e] _ le_rfl]
  · rwa [forgeBy_append_iff Sch P ω F i x₀ dt hmj]

/-- From phase `K` on, a phase entry keeps the view and the state. -/
theorem simInv_step_of_le (K : ℕ) (i : Fin np) (ω : Seed Tx Hash np n Hz PK SK)
    {log : List (LogEvOf X Tx Hash np Hz)} {j : ℕ}
    {v : TreeView (Option (Fin np)) (Block Tx Hash (Fin np))}
    {N : @GlobalState Tx Hash (Fin np) S (ω.params P) (ω.bparams P)}
    {l : List (Block Tx Hash (Fin np) × Sig)} (hI : SimInv P Sch F x₀ dt Tree K i ω log j v N l)
    (x : X) (hKj : K ≤ j) :
    SimInv P Sch F x₀ dt Tree K i ω (log ++ [.inr (.step x)]) (j + 1) v N l := by
  obtain ⟨hjl, hv, hN, hl, hnf⟩ := hI
  have hm : min (j + 1) K = min j K := by omega
  have hmj : min j K ≤ (steps log).length := by omega
  refine ⟨?_, ?_, ?_, hl, ?_⟩
  · simp [hjl, steps, stepOf]
  · rw [hv, viewE_succ_of_le P Sch F x₀ dt Tree K ω hKj hjl.le]
  · rw [hm, hN, sTrace_append_of_le Sch P ω F false x₀ dt hmj _ _ le_rfl]
  · rwa [hm, forgeBy_append_iff Sch P ω F i x₀ dt hmj]

/-- Before phase `K`, a phase entry whose phase forges no block of party `i` moves the view and
the state to the next phase. -/
theorem simInv_step_of_lt (K : ℕ) (i : Fin np) (ω : Seed Tx Hash np n Hz PK SK)
    {log : List (LogEvOf X Tx Hash np Hz)} {j : ℕ}
    {v : TreeView (Option (Fin np)) (Block Tx Hash (Fin np))}
    {N : @GlobalState Tx Hash (Fin np) S (ω.params P) (ω.bparams P)}
    {l : List (Block Tx Hash (Fin np) × Sig)} (hI : SimInv P Sch F x₀ dt Tree K i ω log j v N l)
    (x : X) (hjK : j < K)
    (hF : ¬∃ c ∈ phaseCalls Sch (P.withTx (txOf dt (log ++ [.inr (.step x)]))) ω
        (F.at (scriptOfD x₀ (log ++ [(.inr (.step x) : LogEvOf X Tx Hash np Hz)]))) N,
      ForgedBy Sch ω (F.at (scriptOfD x₀ (log ++ [.inr (.step x)]))) i c)
    (l' : List (Block Tx Hash (Fin np) × Sig))
    (hl' : ∀ b ∈ l'.map Prod.fst, b ∈ hb (P.withTx (txOf dt (log ++ [.inr (.step x)])))
      (F.at (scriptOfD x₀ (log ++ [.inr (.step x)]))) (ω := ω)
        (sPhase Sch (P.withTx (txOf dt (log ++ [.inr (.step x)]))) ω
          (F.at (scriptOfD x₀ (log ++ [.inr (.step x)]))) false N)) :
    SimInv P Sch F x₀ dt Tree K i ω (log ++ [.inr (.step x)]) (j + 1)
      (vNext P Tree ω v (sPhase Sch (P.withTx (txOf dt (log ++ [.inr (.step x)]))) ω
        (F.at (scriptOfD x₀ (log ++ [.inr (.step x)]))) false N))
      (sPhase Sch (P.withTx (txOf dt (log ++ [.inr (.step x)]))) ω
        (F.at (scriptOfD x₀ (log ++ [.inr (.step x)]))) false N) l' := by
  obtain ⟨hjl, hv, hN, hl, hnf⟩ := hI
  rw [min_eq_left hjK.le] at hN hnf
  have hm : min (j + 1) K = j + 1 := min_eq_left hjK
  have hsnoc := sTrace_snoc_step Sch P ω F false x₀ dt hjl.le [.inr (.step x)]
  have happ := sTrace_append_of_le Sch P ω F false x₀ dt hjl.le [.inr (.step x)] j le_rfl
  refine ⟨?_, ?_, ?_, hl', ?_⟩
  · simp [hjl, steps, stepOf]
  · rw [viewE_succ P Sch F x₀ dt Tree K ω hjK hjl.le, hsnoc, hv, hN]
  · rw [hm, hsnoc, hN]
  · rw [hm, traceCalls_succ]
    rintro ⟨c, hc, hfc⟩
    rcases List.mem_append.1 hc with hc | hc
    · exact hnf ((forgeBy_append_iff Sch P ω F i x₀ dt hjl.le _).1 ⟨c, hc, hfc⟩)
    · rw [happ, ← hN] at hc
      exact hF ⟨c, hc, hfc⟩

/-- **The forger simulates the run.** Let `t` be a state of `chainSimω` for the seed `ω` with the
key pair `(pk, sk)` for party `i`, whose seed is unset or this seed, and let the forger's view,
state and signing queries satisfy the invariant `SimInv` for the log of `t`. Then the
probability that the final log of the remaining `m` activations of the environment `Z` from `t`
contains a forgery of party `i` is at most the probability that the forger's loop, run against
the signing oracle of `sk`, outputs a message with a valid signature under `pk` that it did not
query. -/
theorem simLoop_spec (K Δ : ℕ) (i : Fin np) (pk : PK) (sk : SK) (ω : Seed Tx Hash np n Hz PK SK)
    {ζ : Type} (Z : Strat ζ (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) :
    ∀ (m : ℕ) (z : ζ) (h : Heap) (t : SimStE Tx Hash np n Hz PK SK X) (b : Bool)
      (v : TreeView (Option (Fin np)) (Block Tx Hash (Fin np)))
      (N : @GlobalState Tx Hash (Fin np) S (ω.params P) (ω.bparams P))
      (l : List (Block Tx Hash (Fin np) × Sig)),
      t.1.1.getD (ω.withKey i (pk, sk)) = ω.withKey i (pk, sk) →
      SimInv P Sch F x₀ dt Tree K i (ω.withKey i (pk, sk)) t.1.2.1 t.1.2.2.1 v N l →
      prTrue (SPComp.bind (loop (chainSimω P Sch F x₀ dt Tree K Δ (ω.withKey i (pk, sk)))
          (fun _ => false) Z m (z, t, b)) fun c =>
            SPComp.pure (forgeEv P Sch F x₀ dt K i (ω.withKey i (pk, sk)) c.2.1)) h ≤
        ((OracleAdv.run (signOracle Sch sk)
            (simLoop P Sch F x₀ dt Tree K Δ i pk ω Z m z h t.1.2.1 t.1.2.2.1 v t.2 N) l).map
          fun x => Sch.verify pk x.1.1 x.1.2 && !(x.2.map Prod.fst).contains x.1.1) true := by
  intro m
  induction m with
  | zero =>
    intro z h t b v N l _ hI
    obtain ⟨hjl, -, hN, hl, hnf⟩ := hI
    simp only [loop, SPComp.pure_bind, prTrue_pure]
    by_cases hF : forgeEv P Sch F x₀ dt K i (ω.withKey i (pk, sk)) t = true
    · rw [if_pos hF]
      have hF' : ForgeBy Sch (P.withTx (txOf dt t.1.2.1)) (ω.withKey i (pk, sk))
          (F.at (scriptOfD x₀ t.1.2.1)) K i := by
        simpa [forgeEv] using hF
      unfold ForgeBy at hF'
      have hcalls := traceCalls_add Sch (P.withTx (txOf dt t.1.2.1))
        (F.at (scriptOfD x₀ t.1.2.1)) (ω.withKey i (pk, sk)) (min t.1.2.2.1 K) (K - t.1.2.2.1)
      rw [show min t.1.2.2.1 K + (K - t.1.2.2.1) = K by omega] at hcalls
      rw [hcalls] at hF'
      obtain ⟨c, hc, hfc⟩ := hF'
      have hc2 : c ∈ (List.range' (min t.1.2.2.1 K) (K - t.1.2.2.1)).flatMap fun k =>
          phaseCalls Sch (P.withTx (txOf dt t.1.2.1)) (ω.withKey i (pk, sk))
            (F.at (scriptOfD x₀ t.1.2.1))
            (sTrace Sch (P.withTx (txOf dt t.1.2.1)) (ω.withKey i (pk, sk))
              (F.at (scriptOfD x₀ t.1.2.1)) false k) := by
        rcases List.mem_append.1 hc with hc | hc
        · exact absurd ⟨c, hc, hfc⟩ hnf
        · exact hc
      subst hN
      obtain ⟨fg, l', hrun, hv, -, hnl⟩ :=
        (simEq_simTraceFrom Sch (P.withTx (txOf dt t.1.2.1)) (F.at (scriptOfD x₀ t.1.2.1)) i pk ω
          sk (min t.1.2.2.1 K) (K - t.1.2.2.1) (fun _ => loseProg P) l hl).2 ⟨c, hc2, hfc⟩
      simp only [simLoop]
      rw [hrun]
      have hw : (Sch.verify pk fg.1 fg.2 && !(l'.map Prod.fst).contains fg.1) = true := by
        simpa [hv] using hnl
      rw [PMF.pure_map, hw, PMF.pure_apply, if_pos rfl]
    · rw [if_neg hF]
      exact bot_le
  | succ m ih =>
    intro z h t b v N l hseed hI
    simp only [loop, SPComp.bind_assoc, simLoop]
    refine prTrue_bind_le_run_rand _ _ _ _ _ _ _ fun a h₁ => ?_
    obtain ⟨z₁, e⟩ := a
    dsimp only
    rw [chainSimω_step_eq, SPComp.pure_bind]
    simp only [hseed, pstNext, leakOf_withKey]
    have hcont : ∀ (v' : TreeView (Option (Fin np)) (Block Tx Hash (Fin np)))
        (N' : @GlobalState Tx Hash (Fin np) S (ω.params P) (ω.bparams P))
        (l' : List (Block Tx Hash (Fin np) × Sig)),
        SimInv P Sch F x₀ dt Tree K i (ω.withKey i (pk, sk)) (t.1.2.1 ++ [e])
          (phaseNext t.1.2.2.1 e) v' N' l' →
        prTrue (SPComp.bind (Z.obs z₁ (((cnNext Δ t.2 (reqJ t.1.2.2.1 e)).2.1, v'), leakOf ω e))
          fun z' => SPComp.bind (loop (chainSimω P Sch F x₀ dt Tree K Δ (ω.withKey i (pk, sk)))
            (fun _ => false) Z m (z', ((some (ω.withKey i (pk, sk)), t.1.2.1 ++ [e],
              phaseNext t.1.2.2.1 e, v', leakOf ω e), (cnNext Δ t.2 (reqJ t.1.2.2.1 e)).1),
              b || false)) fun c =>
            SPComp.pure (forgeEv P Sch F x₀ dt K i (ω.withKey i (pk, sk)) c.2.1)) h₁ ≤
        ((OracleAdv.run (signOracle Sch sk)
            (.rand (Z.obs z₁ (((cnNext Δ t.2 (reqJ t.1.2.2.1 e)).2.1, v'), leakOf ω e) h₁)
              fun o' => match o' with
                | none => loseProg P
                | some (z₂, h₂) =>
                  simLoop P Sch F x₀ dt Tree K Δ i pk ω Z m z₂ h₂ (t.1.2.1 ++ [e])
                    (phaseNext t.1.2.2.1 e) v' (cnNext Δ t.2 (reqJ t.1.2.2.1 e)).1 N') l').map
          fun x => Sch.verify pk x.1.1 x.1.2 && !(x.2.map Prod.fst).contains x.1.1) true :=
      fun v' N' l' hI' => prTrue_bind_le_run_rand _ _ _ _ _ _ _ fun z₂ h₂ =>
        ih z₂ h₂ _ _ v' N' l' rfl hI'
    rcases e with tx | (x | d)
    · have hI' := simInv_append P Sch F x₀ dt Tree K i (ω.withKey i (pk, sk)) hI (.inl tx) rfl
      rw [phaseNext_of_stepOf_none _ (.inl tx) rfl] at hcont ⊢
      rw [← hI'.2.1, simEv_of_stepOf_none P Sch F x₀ dt Tree (.inl tx) rfl]
      exact hcont v N l hI'
    · dsimp only [phaseNext] at hcont ⊢
      by_cases hjK : t.1.2.2.1 < K
      · simp only [simEv, if_pos hjK]
        have hs := simEq_simPhase Sch (P.withTx (txOf dt (t.1.2.1 ++ [.inr (.step x)])))
          (F.at (scriptOfD x₀ (t.1.2.1 ++ [.inr (.step x)]))) i pk ω sk N
        refine hs.le_run _ _ _ _ _ _ _ _ l hI.2.2.2.1 (prTrue_le_one _ _) fun l' hl' hF => ?_
        have hI' := simInv_step_of_lt P Sch F x₀ dt Tree K i (ω.withKey i (pk, sk)) hI x hjK
          (fun ⟨c, hc, hfc⟩ => hF c hc hfc) l' hl'
        rw [vNext_withKey] at hI'
        rw [← hI'.2.1]
        have hc := hcont _ _ _ hI'
        exact hc
      · simp only [simEv, if_neg hjK]
        have hI' := simInv_step_of_le P Sch F x₀ dt Tree K i (ω.withKey i (pk, sk)) hI x
          (not_lt.1 hjK)
        rw [← hI'.2.1]
        exact hcont v N l hI'
    · have hI' := simInv_append P Sch F x₀ dt Tree K i (ω.withKey i (pk, sk)) hI (.inr (.hash d))
        rfl
      rw [phaseNext_of_stepOf_none _ (.inr (.hash d)) rfl] at hcont ⊢
      rw [← hI'.2.1, simEv_of_stepOf_none P Sch F x₀ dt Tree (.inr (.hash d)) rfl]
      exact hcont v N l hI'

/-- **Forging a block of party `i` against an environment.** Over the seed distribution
`seedDist Sch H cd`, the probability that the final log of the run of the environment `Z`
against `chainSimω` contains a forgery of party `i` is at most the EUF-CMA advantage of the
explicit adversary `toEUFAdversary (forgerE … Z i)` against `Sch`. -/
theorem prob_forgeE_le (μ : PMF (Option (Fin np))) (W K Δ : ℕ) {ζ : Type}
    (Z : Env (Strat ζ (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) ζ) (i : Fin np) :
    ∑' ω, seedDist Sch H cd μ P.h0 W n ω *
        prFinal (chainSimω P Sch F x₀ dt Tree K Δ ω) (forgeEv P Sch F x₀ dt K i ω) Z ≤
      eufcmaAdvantage Sch.toSigScheme
        (toEUFAdversary (forgerE P Sch F x₀ dt Tree H cd μ W K Δ Z i)) := by
  have hseed := seedDist_withKey (n := n) Sch H cd μ P.h0 W i
  rw [PMF.bind_comm, PSigScheme.keyDist, PMF.bind_map] at hseed
  rw [eufcmaAdvantage_toEUFAdversary, eufDist, PMF.bind_apply]
  conv_lhs => rw [← hseed]
  rw [PMF.tsum_bind_mul]
  refine ENNReal.tsum_le_tsum fun kr => ?_
  gcongr
  simp only [Function.comp_apply, forgerE, OracleAdv.run_rand, PMF.map_bind]
  rw [PMF.tsum_bind_mul, PMF.bind_apply]
  refine ENNReal.tsum_le_tsum fun ω => ?_
  gcongr
  rw [tsum_eq_single (ω.withKey i (Sch.keygen kr)) fun b hb => by simp [PMF.pure_apply, hb],
    PMF.pure_apply, if_pos rfl, one_mul]
  unfold prFinal run
  exact simLoop_spec P Sch F x₀ dt Tree K Δ i (Sch.keygen kr).1 (Sch.keygen kr).2 ω Z.input
    Z.input.rounds Z.input.init Z.heap _ false _ _ [] rfl
    ⟨rfl, (viewE_zero P Sch F x₀ dt Tree K _ []).symm, rfl, by simp,
      by simp [chainSimω, Hybrid.withSub, chainHybridE, traceCalls]⟩

/-- **The fixed-adversary forger is the zero-round instance.** The forger
`forger Sch P A H cd μ W K i` of the adversary `A` is the forger `forgerE` of an environment
without activations, for the constant family of `A` and the transaction selection `P.txSel`. -/
theorem forger_eq_env (A : Adversary Tx Hash np n Hz PK Sig) (μ : PMF (Option (Fin np)))
    (W K Δ : ℕ) {ζ : Type}
    (Z : Env (Strat ζ (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) ζ) (hZ : Z.input.rounds = 0)
    (i : Fin np) :
    forger Sch P A H cd μ W K i =
      forgerE P Sch (AdvFamily.const A) x₀ P.txSel Tree H cd μ W K Δ Z i := by
  funext pk
  unfold forger forgerE
  congr 1
  funext ω
  rw [hZ, forgerProg, simTrace_eq_from]
  rfl

/-- The forger `forger` of a fixed adversary has the advantage of the forger `forgerE` of an
environment without activations. -/
theorem forger_adv_eq_env (A : Adversary Tx Hash np n Hz PK Sig) (μ : PMF (Option (Fin np)))
    (W K Δ : ℕ) {ζ : Type}
    (Z : Env (Strat ζ (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) ζ) (hZ : Z.input.rounds = 0)
    (i : Fin np) :
    eufcmaAdvantage Sch.toSigScheme (toEUFAdversary (forger Sch P A H cd μ W K i)) =
      eufcmaAdvantage Sch.toSigScheme (toEUFAdversary
        (forgerE P Sch (AdvFamily.const A) x₀ P.txSel Tree H cd μ W K Δ Z i)) := by
  rw [forger_eq_env P Sch x₀ Tree H cd A μ W K Δ Z hZ i]

/-! ## The failure bound against an environment -/

/-- A property of the final state that implies one of finitely many properties has at most the
sum of their probabilities. -/
theorem prFinal_le_sum {τ E O ζ ι : Type} [Fintype ι] (S' : Sys τ E O) (q : τ → Bool)
    (r : ι → τ → Bool) (h : ∀ t, q t = true → ∃ k, r k t = true) (Z : Env (Strat ζ E O) ζ) :
    prFinal S' q Z ≤ ∑ k, prFinal S' (r k) Z := by
  unfold prFinal
  simp only [prTrue_bind_eq_weighted]
  rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
  refine ENNReal.tsum_le_tsum fun p => ?_
  rw [← Finset.mul_sum]
  gcongr
  rcases p with _ | ⟨c, h'⟩
  · simp
  · dsimp only
    simp only [prTrue_pure]
    by_cases hq : q c.2.1 = true
    · obtain ⟨k, hk⟩ := h _ hq
      rw [if_pos hq]
      refine le_trans ?_ (Finset.single_le_sum (f := fun j => if r j c.2.1 = true then (1 : ℝ≥0∞)
        else 0) (fun _ _ => bot_le) (Finset.mem_univ k))
      simp [hk]
    · rw [if_neg hq]
      exact bot_le

/-- A property of the final state that is constant has probability at most its indicator. -/
theorem prFinal_const_le {τ E O ζ : Type} (S' : Sys τ E O) (c : Bool) (Z : Env (Strat ζ E O) ζ) :
    prFinal S' (fun _ => c) Z ≤ if c then 1 else 0 := by
  cases c
  · simpa using prFinal_le_sum S' (fun _ => false) (ι := Empty) (fun e => e.elim) (by simp) Z
  · exact prTrue_le_one _ _

open Classical in
/-- The collision event on the final log of a state: some state of the first `K` phases of the
execution of the log is not collision free. -/
noncomputable def collEv (K : ℕ) (ω : Seed Tx Hash np n Hz PK SK)
    (t : SimStE Tx Hash np n Hz PK SK X) : Bool :=
  decide (∃ j ≤ K, letI := ω.params P; letI := ω.bparams P
    ¬collision_free (sTrace Sch { P with txSel := txOf dt t.1.2.1 } ω
      (F.at (scriptOfD x₀ t.1.2.1)) false j))

/-- **Hash collisions against an environment.** Over the seed distribution `seedDist Sch H cd`,
the probability that the final log of the run of the environment `Z` against `chainSimω` has a
state of its first `K` phases that is not collision free is at most the collision-resistance
advantage of the explicit adversary `collFinderE … Z`. -/
theorem prob_collisionE_le (μ : PMF (Option (Fin np))) (W K Δ : ℕ) (hHz : K + 1 ≤ Hz)
    (hGB : P.GB.sl ≤ 1) {ζ : Type}
    (Z : Env (Strat ζ (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) ζ) :
    ∑' ω, seedDist Sch H cd μ P.h0 W n ω *
        prFinal (chainSimω P Sch F x₀ dt Tree K Δ ω) (collEv P Sch F x₀ dt K ω) Z ≤
      CR_Search_Advantage H (collFinderE P Sch F x₀ dt Tree H cd μ W K Δ Z) := by
  refine le_trans (le_of_eq ?_) (prob_collisionG_le Sch P H cd μ W K hHz hGB
    (fun ω => SPComp.atHeap Z.heap (finalLog P Sch F x₀ dt Tree K Δ ω Z.input)) (txOf dt)
    (fun log => F.at (scriptOfD x₀ log)))
  rw [prTrue_bind_sampleFrom]
  refine tsum_congr fun ω => ?_
  rw [ofPMF_apply_some, prTrue_bind_atHeap]
  congr 1
  unfold prFinal finalLog SPComp.map
  rw [SPComp.bind_assoc]
  simp only [SPComp.pure_bind]
  rfl

open Classical in
/-- **The slot conditions against an environment.** The slot conditions depend on the seed only:
over the seed distribution, the probability that they fail or that the leader string is not
padded with honest slots, at the end of the run of any environment, is at most `slotBound`. -/
theorem prob_slotE_le (hh0 : is_honest P.h0 = true) (μ : PMF (Option (Fin np))) (W K Δ d w : ℕ)
    (ε : ℝ) (hε : 0 ≤ ε) (hγ : 2 * pA (kindLaw μ) ≤ pH (kindLaw μ))
    (hw : (w : ℝ) ≤ d * (pH (kindLaw μ) - pA (kindLaw μ)))
    (h3 : (3 : ℝ) ≤ d * (pH (kindLaw μ) - 2 * pA (kindLaw μ))) {ζ : Type}
    (Z : Env (Strat ζ (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) ζ) :
    ∑' ω, seedDist Sch H cd μ P.h0 W n ω *
        prFinal (chainSimω P Sch F x₀ dt Tree K Δ ω)
          (fun _ => decide (SlotBad (kindLaw μ) n d w ε ω.κ ∨ ¬PaddedFrom W ω.κ)) Z ≤
      slotBound (kindLaw μ) n d w ε := by
  calc _ ≤ ∑' ω, seedDist Sch H cd μ P.h0 W n ω *
        (if decide (SlotBad (kindLaw μ) n d w ε ω.κ ∨ ¬PaddedFrom W ω.κ) then 1 else 0) :=
        ENNReal.tsum_le_tsum fun ω => by gcongr; exact prFinal_const_le _ _ _
    _ = (seedDist Sch H cd μ P.h0 W n).toOuterMeasure
          {ω | ω.κ ∈ {κ | SlotBad (kindLaw μ) n d w ε κ} ∪ {κ | ¬PaddedFrom W κ}} := by
        rw [PMF.toOuterMeasure_apply]
        refine tsum_congr fun ω => ?_
        by_cases h : SlotBad (kindLaw μ) n d w ε ω.κ ∨ ¬PaddedFrom W ω.κ
        · simp [h, Set.indicator]
        · simp [h, Set.indicator]
    _ ≤ _ := by
        rw [seedDist_kind Sch H cd μ hh0]
        refine (MeasureTheory.measure_union_le _ _).trans ?_
        rw [kindDist_padded, add_zero]
        exact prob_slotBad_le (kindLaw μ) W n d w hε hγ hw h3

/-- **The deterministic step for a log.** Outside the bad events, the property `GoodE` holds
for the execution of the seed `ω` and the log `log`. -/
theorem goodE_of_not_bad (hP : ProtocolHyp P) (hTree : Tree.Longest) (ν : PMF SlotKind)
    (K d w : ℕ) (ε : ℝ) (ω : Seed Tx Hash np n Hz PK SK) (log : List (LogEvOf X Tx Hash np Hz))
    {W : ℕ} (hd3 : 3 ≤ d) (hwd : w ≤ d) (hWn : W + d ≤ n) (hn : K + 2 ≤ n)
    (hslot : ¬SlotBad ν n d w ε ω.κ) (hpad : PaddedFrom W ω.κ)
    (hcf : ∀ j ≤ K, letI := ω.params P; letI := ω.bparams P;
      collision_free (sTrace Sch (P.withTx (txOf dt log)) ω (F.at (scriptOfD x₀ log)) false j))
    (hforge : ¬Forge Sch (P.withTx (txOf dt log)) ω (F.at (scriptOfD x₀ log)) K) :
    GoodE P Sch F x₀ dt Tree ν K d w ε ω log :=
  good_of_not_bad (P.withTx (txOf dt log)) Sch (F.at (scriptOfD x₀ log)) Tree ν K d w ε
    (hP.withTx _) hTree ω hd3 hwd hWn hn hslot hpad hcf hforge

/-- **The failure bound of PoS-NSB against an environment**: the Chernoff-Hoeffding bound
`slotBound` on the slot conditions, the collision-resistance advantage of the explicit collision
finder `collFinderE … Z`, and the sum over the parties `i` of the EUF-CMA advantages of the
explicit forgers `toEUFAdversary (forgerE … Z i)`. -/
noncomputable def posFailE (μ : PMF (Option (Fin np))) (W K Δ d w : ℕ) (ε : ℝ) {ζ : Type}
    (Z : Env (Strat ζ (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) ζ) : ℝ≥0∞ :=
  slotBound (kindLaw μ) n d w ε +
    CR_Search_Advantage H (collFinderE P Sch F x₀ dt Tree H cd μ W K Δ Z) +
    ∑ i : Fin np, eufcmaAdvantage Sch.toSigScheme
      (toEUFAdversary (forgerE P Sch F x₀ dt Tree H cd μ W K Δ Z i))

open Classical in
/-- **Security of PoS-NSB against an environment.** Let the environment `Z` drive the protocol
for seeds drawn from `seedDist Sch H cd`. Under the hypotheses of `pos_nsb_security`, the
probability that chain growth, chain quality, common prefix or the honest tip fails for the
first `K` phases of the execution of the final log of the run of `Z` against `chainSimω` is at
most `posFailE … Z`: `slotBound (kindLaw μ) n d w ε + CR_Search_Advantage H (collFinderE … Z) +
∑ᵢ eufcmaAdvantage Sch.toSigScheme (toEUFAdversary (forgerE … Z i))`. -/
theorem pos_nsb_securityE (hP : ProtocolHyp P) (hTree : Tree.Longest)
    (μ : PMF (Option (Fin np))) (W K Δ d w : ℕ) (ε : ℝ)
    (hwd : w ≤ d) (hWn : W + d ≤ n) (hn : K + 2 ≤ n) (hHz : K + 1 ≤ Hz)
    (hε : 0 ≤ ε) (hγ : 2 * pA (kindLaw μ) ≤ pH (kindLaw μ))
    (hw : (w : ℝ) ≤ d * (pH (kindLaw μ) - pA (kindLaw μ)))
    (h3 : (3 : ℝ) ≤ d * (pH (kindLaw μ) - 2 * pA (kindLaw μ))) {ζ : Type}
    (Z : Env (Strat ζ (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) ζ) :
    ∑' ω, seedDist Sch H cd μ P.h0 W n ω *
        prFinal (chainSimω P Sch F x₀ dt Tree K Δ ω)
          (fun t => decide (¬GoodE P Sch F x₀ dt Tree (kindLaw μ) K d w ε ω t.1.2.1)) Z ≤
      posFailE P Sch F x₀ dt Tree H cd μ W K Δ d w ε Z := by
  have hd3 := three_le_of_cp (kindLaw μ) h3
  have hpt : ∀ ω : Seed Tx Hash np n Hz PK SK,
      prFinal (chainSimω P Sch F x₀ dt Tree K Δ ω)
          (fun t => decide (¬GoodE P Sch F x₀ dt Tree (kindLaw μ) K d w ε ω t.1.2.1)) Z ≤
        prFinal (chainSimω P Sch F x₀ dt Tree K Δ ω)
            (fun _ => decide (SlotBad (kindLaw μ) n d w ε ω.κ ∨ ¬PaddedFrom W ω.κ)) Z +
          (prFinal (chainSimω P Sch F x₀ dt Tree K Δ ω) (collEv P Sch F x₀ dt K ω) Z +
            ∑ i : Fin np,
              prFinal (chainSimω P Sch F x₀ dt Tree K Δ ω) (forgeEv P Sch F x₀ dt K i ω) Z) := by
    intro ω
    refine (prFinal_le_sum _ _ (fun k : Option (Option (Fin np)) => match k with
      | none => fun _ => decide (SlotBad (kindLaw μ) n d w ε ω.κ ∨ ¬PaddedFrom W ω.κ)
      | some none => collEv P Sch F x₀ dt K ω
      | some (some i) => forgeEv P Sch F x₀ dt K i ω) ?_ Z).trans (le_of_eq ?_)
    · intro t ht
      by_contra hno
      simp only [not_exists, Bool.not_eq_true] at hno
      have h0 := hno none
      have h1 := hno (some none)
      simp only [decide_eq_false_iff_not, not_or, not_not] at h0
      simp only [collEv, decide_eq_false_iff_not, not_exists, not_and, not_not] at h1
      refine of_decide_eq_true ht (goodE_of_not_bad P Sch F x₀ dt Tree hP hTree (kindLaw μ) K d w ε
        ω t.1.2.1 hd3 hwd hWn hn h0.1 h0.2 h1 fun hF => ?_)
      obtain ⟨i, hi⟩ := forge_iff_exists Sch _ ω _ K hF
      have h2 := hno (some (some i))
      simp only [forgeEv, decide_eq_false_iff_not] at h2
      exact h2 hi
    · simp only [Fintype.sum_option]
  calc _ ≤ ∑' ω, seedDist Sch H cd μ P.h0 W n ω *
        (prFinal (chainSimω P Sch F x₀ dt Tree K Δ ω)
            (fun _ => decide (SlotBad (kindLaw μ) n d w ε ω.κ ∨ ¬PaddedFrom W ω.κ)) Z +
          (prFinal (chainSimω P Sch F x₀ dt Tree K Δ ω) (collEv P Sch F x₀ dt K ω) Z +
            ∑ i : Fin np,
              prFinal (chainSimω P Sch F x₀ dt Tree K Δ ω) (forgeEv P Sch F x₀ dt K i ω) Z)) :=
        ENNReal.tsum_le_tsum fun ω => by gcongr; exact hpt ω
    _ = ∑' ω, seedDist Sch H cd μ P.h0 W n ω *
          prFinal (chainSimω P Sch F x₀ dt Tree K Δ ω)
            (fun _ => decide (SlotBad (kindLaw μ) n d w ε ω.κ ∨ ¬PaddedFrom W ω.κ)) Z +
        (∑' ω, seedDist Sch H cd μ P.h0 W n ω *
            prFinal (chainSimω P Sch F x₀ dt Tree K Δ ω) (collEv P Sch F x₀ dt K ω) Z +
          ∑ i : Fin np, ∑' ω, seedDist Sch H cd μ P.h0 W n ω *
            prFinal (chainSimω P Sch F x₀ dt Tree K Δ ω) (forgeEv P Sch F x₀ dt K i ω) Z) := by
        simp_rw [mul_add, Finset.mul_sum]
        rw [ENNReal.tsum_add, ENNReal.tsum_add,
          Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
    _ ≤ _ := by
        unfold posFailE
        rw [add_assoc]
        exact add_le_add
          (prob_slotE_le P Sch F x₀ dt Tree H cd hP.leader.h0_honest μ W K Δ d w ε hε hγ hw h3 Z)
          (add_le_add (prob_collisionE_le P Sch F x₀ dt Tree H cd μ W K Δ hHz hP.genesis_slot Z)
            (Finset.sum_le_sum fun i _ => prob_forgeE_le P Sch F x₀ dt Tree H cd μ W K Δ Z i))

/-- The environment without activations, from the empty heap. -/
noncomputable def envNoRounds (x : X) :
    Env (Strat Unit (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) Unit where
  input :=
    { rounds := 0
      init := ()
      next := fun _ => SPComp.pure ((), .inr (.step x))
      obs := fun _ _ => SPComp.pure ()
      next_noFail := fun _ => SPComp.pure_noFail _
      obs_noFail := fun _ _ => SPComp.pure_noFail _ }
  heap := Heap.empty
  dist := fun _ => SPComp.pure true

open Classical in
/-- **The fixed-adversary bound is the zero-round instance.** `pos_nsb_security` for the
adversary `A` follows from `pos_nsb_securityE` for the constant family of `A`, the transaction
selection `P.txSel` and the environment without activations. -/
theorem pos_nsb_security_of_env (A : Adversary Tx Hash np n Hz PK Sig) (hP : ProtocolHyp P)
    (hTree : Tree.Longest) (μ : PMF (Option (Fin np))) (W K d w : ℕ) (ε : ℝ)
    (hwd : w ≤ d) (hWn : W + d ≤ n) (hn : K + 2 ≤ n) (hHz : K + 1 ≤ Hz)
    (hε : 0 ≤ ε) (hγ : 2 * pA (kindLaw μ) ≤ pH (kindLaw μ))
    (hw : (w : ℝ) ≤ d * (pH (kindLaw μ) - pA (kindLaw μ)))
    (h3 : (3 : ℝ) ≤ d * (pH (kindLaw μ) - 2 * pA (kindLaw μ))) :
    (seedDist Sch H cd μ P.h0 W n).toOuterMeasure
        {ω | ¬Good P Sch A Tree (kindLaw μ) K d w ε ω} ≤
      posFail P Sch A H cd μ W K d w ε := by
  have h := pos_nsb_securityE P Sch (AdvFamily.const A) () P.txSel Tree H cd hP hTree μ W K 0 d w
    ε hwd hWn hn hHz hε hγ hw h3 (envNoRounds ())
  unfold posFailE at h
  rw [← collFinder_adv_eq_env P Sch () Tree H cd A μ W K 0 (envNoRounds ()) rfl] at h
  simp only [← forger_adv_eq_env P Sch () Tree H cd A μ W K 0 (envNoRounds ()) rfl] at h
  refine le_trans (le_of_eq ?_) h
  rw [PMF.toOuterMeasure_apply]
  refine tsum_congr fun ω => ?_
  have hg : GoodE P Sch (AdvFamily.const A) () P.txSel Tree (kindLaw μ) K d w ε ω [] ↔
      Good P Sch A Tree (kindLaw μ) K d w ε ω := Iff.rfl
  by_cases hG : Good P Sch A Tree (kindLaw μ) K d w ε ω
  · simp [Set.indicator, hG, hg, prFinal, run, envNoRounds, loop, prTrue_pure, chainSimω,
      Hybrid.withSub, chainHybridE]
  · simp [Set.indicator, hG, hg, prFinal, run, envNoRounds, loop, prTrue_pure, chainSimω,
      Hybrid.withSub, chainHybridE]

end Protocol

end CatCryptCore.Consensus.UC.ChainEnv
