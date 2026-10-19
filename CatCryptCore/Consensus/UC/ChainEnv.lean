/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.UC.Chain
public import CatCryptCore.Consensus.PoSNSB.Prob.Script
public import CatCryptCore.Crypto.UCTransparentAdv

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

## Main results

* `chainSimω_step_pure` — the steps of `chainSimω ω` are deterministic.
* `run_chainSimE` — the run against `chainSimE` is the average over the seed of the runs against
  `chainSimω ω`.
* `phaseView_succ`, `phaseView_succ_of_le` — the view of the next phase extends the trees of the
  view of the current phase by the positions of the next phase, up to phase `K`.
* `collFinder_adv_eq_env` — the collision finder `collFinder` of a fixed adversary `A` has the
  advantage of `collFinderE` for the constant family of `A`, the transaction selection of the
  protocol and an environment without activations.
-/

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

end Protocol

end CatCryptCore.Consensus.UC.ChainEnv
