/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.PoSNSB.Prob.Protocol
public import CatCryptCore.Crypto.OracleSimulation
public import CatCryptCore.Crypto.Assumptions.CR

/-!
# PoS-NSB: forging honest blocks reduces to EUF-CMA

For every adversary `A` against the signed protocol of
`CatCryptCore/Consensus/PoSNSB/Prob/Protocol.lean`, every keyed hash family `H` (`HashScheme`
with a codec `cd` of the block domain) and every party `i`, this file defines an explicit
adaptive oracle adversary `forger Sch P A H cd μ W K i` against the EUF-CMA game of the
signature scheme `Sch` (`eufcmaAdvantage` of `CatCryptCore/Crypto/Signatures/EUFCMA.lean`).
The forger receives the verification key of the game and a signing oracle, samples a seed
(the lottery, the hash key and the key pairs) with one coin flip, runs the real execution with
the key of the game for party `i`, obtains the signatures of the honest blocks of party `i`
from the signing oracle, and outputs the first accepted block of party `i` that the adversary
sends outside the history. Without such a block it queries the genesis block and outputs it
with its signature, which loses.

## Main definitions

* `mapQ g l`: the oracle adversary that runs `g` on every element of `l`.
* `seedDist Sch H cd`: the distribution of the random seed, with a uniformly random key `k`
  of `H` and the hash function `cd.hashOn k`; `ForgeBy`: the adversary of the real execution
  forges a block of party `i`.
* `forger Sch P A H cd μ W K i`: the reduction, an adversary
  `PK → OracleAdv (Block …) Sig (Block … × Sig)`.

## Main results

* `forgerProg_wins`: if the adversary forges a block of party `i` in the real execution for
  the seed `ω` with the key pair `(pk, sk)` for party `i`, every output of the simulation run
  against the signing oracle of `sk` is a winning forgery.
* `prob_forgeBy_le`: `Pr[ForgeBy i] ≤ eufcmaAdvantage Sch.toSigScheme (toEUFAdversary (forger … i))`.
* `prob_forge_le`: `Pr[Forge] ≤ ∑ᵢ eufcmaAdvantage Sch.toSigScheme (toEUFAdversary (forger … i))`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace CatCryptCore.Consensus.PoSNSB

open Parameters BlockParameters Corruption Execution
open CatCrypt.Crypto CatCrypt.Crypto.Signatures CatCrypt.Crypto.Assumptions
open scoped ENNReal

/-- The oracle adversary that runs `g` on every element of a list and returns the list of the
outputs. -/
def mapQ {D R β γ : Type} (g : β → OracleAdv D R γ) : List β → OracleAdv D R (List γ)
  | [] => .ret []
  | b :: bs => (g b).bind fun x => (mapQ g bs).bind fun xs => .ret (x :: xs)

/-! ## The forger -/

section Forger

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ} {PK SK Sig : Type}
  (Sch : PSigScheme (Block Tx Hash (Fin np)) PK SK Sig) [hS : Sch.Deterministic]

/-- The seed `ω` with the key pair `kp` for party `i`. -/
abbrev Seed.withKey (ω : Seed Tx Hash np n Hz PK SK) (i : Fin np) (kp : PK × SK) :
    Seed Tx Hash np n Hz PK SK :=
  { ω with ks := Function.update ω.ks i kp }

/-- The adversary call `c` forges a block of party `i`: it outputs an accepted honest block of
party `i` that is not in the history. -/
def ForgedBy (ω : Seed Tx Hash np n Hz PK SK) (A : Adversary Tx Hash np n Hz PK Sig)
    (i : Fin np) (c : CallInput Tx Hash np A.AdvState) : Prop :=
  ∃ x ∈ (advRaw Sch ω A c).1, sigOK Sch (fun j => (ω.ks j).1) c.sl x = true ∧
    histOK c.hist x = false ∧ (get_block x.1.1).bid = i

/-- **The forging event for party `i`.** Some adversary call in the first `K` phases of the real
execution forges a block of party `i`. -/
def ForgeBy (P : Protocol Tx Hash np n Hz) (ω : Seed Tx Hash np n Hz PK SK)
    (A : Adversary Tx Hash np n Hz PK Sig) (K : ℕ) (i : Fin np) : Prop :=
  ∃ c ∈ traceCalls Sch P ω A K, ForgedBy Sch ω A i c

theorem forge_iff_exists (P : Protocol Tx Hash np n Hz) (ω : Seed Tx Hash np n Hz PK SK)
    (A : Adversary Tx Hash np n Hz PK Sig) (K : ℕ) :
    Forge Sch P ω A K → ∃ i, ForgeBy Sch P ω A K i := by
  rintro ⟨c, hc, x, hx, h1, h2⟩
  exact ⟨_, c, hc, x, hx, h1, h2, rfl⟩

/-- The first output of party `i` that the network accepts although it is an honest block
outside the history. -/
def findForgery {AdvState : Type} (i : Fin np) (pks : Fin np → PK)
    (c : CallInput Tx Hash np AdvState) (out : AdvOut Tx Hash np Sig) :
    Option (Block Tx Hash (Fin np) × Sig) :=
  (out.find? fun x => sigOK Sch pks c.sl x && !histOK c.hist x &&
    decide ((get_block x.1.1).bid = i)).map fun x => (get_block x.1.1, x.1.2)

theorem findForgery_none {AdvState : Type} {i : Fin np} {pks : Fin np → PK}
    {c : CallInput Tx Hash np AdvState} {out : AdvOut Tx Hash np Sig}
    (h : findForgery Sch i pks c out = none) :
    ¬∃ x ∈ out, sigOK Sch pks c.sl x = true ∧ histOK c.hist x = false ∧
      (get_block x.1.1).bid = i := by
  rintro ⟨x, hx, h1, h2, h3⟩
  simp only [findForgery, Option.map_eq_none_iff, List.find?_eq_none] at h
  have := h x hx
  simp [h1, h2, h3] at this

theorem findForgery_some {AdvState : Type} {i : Fin np} {pks : Fin np → PK}
    {c : CallInput Tx Hash np AdvState} {out : AdvOut Tx Hash np Sig}
    {m : Block Tx Hash (Fin np)} {σ : Sig} (h : findForgery Sch i pks c out = some (m, σ)) :
    Sch.verify (pks i) m σ = true ∧ m ∉ c.hist.map get_block := by
  simp only [findForgery, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, hxm⟩ := h
  have := List.find?_some hx
  simp only [Prod.mk.injEq] at hxm
  obtain ⟨rfl, rfl⟩ := hxm
  simp only [sigOK, histOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
    Bool.not_true, Bool.or_eq_false_iff, Bool.or_eq_true] at this
  obtain ⟨⟨⟨_, hv⟩, hc, hm⟩, hi⟩ := this
  refine ⟨?_, by simpa using hm⟩
  rcases hv with hv | hv
  · rw [hv] at hc; exact absurd hc (by decide)
  · rw [← hi]; exact hv

theorem findForgery_isSome {AdvState : Type} {i : Fin np} {pks : Fin np → PK}
    {c : CallInput Tx Hash np AdvState} {out : AdvOut Tx Hash np Sig}
    (h : ∃ x ∈ out, sigOK Sch pks c.sl x = true ∧ histOK c.hist x = false ∧
      (get_block x.1.1).bid = i) :
    ∃ m σ, findForgery Sch i pks c out = some (m, σ) := by
  cases hf : findForgery Sch i pks c out with
  | none => exact absurd h (findForgery_none Sch hf)
  | some fg => exact ⟨fg.1, fg.2, rfl⟩

theorem findForgery_eq_none {AdvState : Type} {i : Fin np} {pks : Fin np → PK}
    {c : CallInput Tx Hash np AdvState} {out : AdvOut Tx Hash np Sig}
    (h : ¬∃ x ∈ out, sigOK Sch pks c.sl x = true ∧ histOK c.hist x = false ∧
      (get_block x.1.1).bid = i) :
    findForgery Sch i pks c out = none := by
  simp only [findForgery, Option.map_eq_none_iff, List.find?_eq_none]
  intro x hx hx'
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at hx'
  exact h ⟨x, hx, hx'.1.1, hx'.1.2, hx'.2⟩

variable (P : Protocol Tx Hash np n Hz) (A : Adversary Tx Hash np n Hz PK Sig) (i : Fin np)
  (pk : PK) (ω : Seed Tx Hash np n Hz PK SK)

/-- The verification keys of the simulation: `pk` for party `i`, the keys of `ω` for the other
parties. -/
def simPks : Fin np → PK := fun j => if j = i then pk else (ω.ks j).1

/-- The public information of the simulation. -/
def simPub : PubInfo Tx Hash np n Hz PK := (ω.L, ω.f, simPks i pk ω)

/-- The signature of a block in the simulation: from the signing oracle for party `i`, with
the keys of `ω` for the other parties. -/
def simSign (b : Block Tx Hash (Fin np)) :
    OracleAdv (Block Tx Hash (Fin np)) Sig (Block Tx Hash (Fin np) × Sig) :=
  if b.bid = i then .query b fun σ => .ret (b, σ) else .ret (b, hS.dsign (ω.ks b.bid).2 b)

/-- The signatures of the honest blocks of a history in the simulation. -/
def simTable (hist : History Tx Hash (Fin np)) :
    OracleAdv (Block Tx Hash (Fin np)) Sig (List (Block Tx Hash (Fin np) × Sig)) :=
  mapQ (simSign Sch i ω) ((hist.map get_block).filter honest_block)

/-- An adversary call in the simulation. -/
def simAdv (c : CallInput Tx Hash np A.AdvState) :
    OracleAdv (Block Tx Hash (Fin np)) Sig (AdvOut Tx Hash np Sig × A.AdvState) :=
  (simTable Sch i ω c.hist).bind fun tbl => .ret (match c.msgs with
    | none => A.bake (simPub i pk ω) c.sl c.hist tbl c.mb c.st
    | some ms => A.rcv (simPub i pk ω) ms c.sl c.hist tbl c.mb c.st)

section Correct

variable (sk : SK)

theorem simPks_eq : simPks i pk ω = fun j => ((ω.withKey i (pk, sk)).ks j).1 := by
  funext j
  by_cases h : j = i
  · subst h; simp [simPks]
  · simp [simPks, h]

theorem simPub_eq : simPub i pk ω = (ω.withKey i (pk, sk)).pub := by
  simp only [simPub, Seed.pub, simPks_eq i pk ω sk]

/-- Against the signing oracle of `sk`, the simulated signatures of a list of blocks are the
signatures under the keys of `ω` with `(pk, sk)` for party `i`, and only blocks of the list are
queried. -/
theorem run_mapQ_simSign (bs : List (Block Tx Hash (Fin np)))
    (l : List (Block Tx Hash (Fin np) × Sig)) :
    ∃ log, OracleAdv.run (signOracle Sch sk) (mapQ (simSign Sch i ω) bs) l =
      PMF.pure (bs.map (fun b => (b, hS.dsign ((ω.withKey i (pk, sk)).ks b.bid).2 b)),
        l ++ log) ∧ ∀ b ∈ log.map Prod.fst, b ∈ bs := by
  induction bs generalizing l with
  | nil => exact ⟨[], by simp [mapQ], by simp⟩
  | cons b bs ih =>
    by_cases h : b.bid = i
    · obtain ⟨log, hr, hlog⟩ := ih (l ++ [(b, hS.dsign sk b)])
      refine ⟨(b, hS.dsign sk b) :: log, ?_, ?_⟩
      · simp only [mapQ, simSign, h, if_true, OracleAdv.run_bind, run_query_signOracle_det,
          OracleAdv.run_ret, PMF.pure_bind, hr]
        simp [h]
      · intro b' hb'
        simp only [List.map_cons, List.mem_cons] at hb' ⊢
        rcases hb' with rfl | hb'
        · exact Or.inl rfl
        · exact Or.inr (hlog b' hb')
    · obtain ⟨log, hr, hlog⟩ := ih l
      refine ⟨log, ?_, fun b' hb' => List.mem_cons_of_mem _ (hlog b' hb')⟩
      simp only [mapQ, simSign, h, if_false, OracleAdv.bind_ret, OracleAdv.run_bind,
        OracleAdv.run_ret, PMF.pure_bind, hr]
      simp [h]

theorem run_simTable (hist : History Tx Hash (Fin np))
    (l : List (Block Tx Hash (Fin np) × Sig)) :
    ∃ log, OracleAdv.run (signOracle Sch sk) (simTable Sch i ω hist) l =
      PMF.pure (sigTable Sch (ω.withKey i (pk, sk)).ks hist, l ++ log) ∧
      ∀ b ∈ log.map Prod.fst, b ∈ hist.map get_block := by
  obtain ⟨log, hr, hlog⟩ := run_mapQ_simSign Sch i pk ω sk
    ((hist.map get_block).filter honest_block) l
  exact ⟨log, hr, fun b hb => (List.mem_filter.1 (hlog b hb)).1⟩

theorem run_simAdv (c : CallInput Tx Hash np A.AdvState)
    (l : List (Block Tx Hash (Fin np) × Sig)) :
    ∃ log, OracleAdv.run (signOracle Sch sk) (simAdv Sch A i pk ω c) l =
      PMF.pure (advRaw Sch (ω.withKey i (pk, sk)) A c, l ++ log) ∧
      ∀ b ∈ log.map Prod.fst, b ∈ c.hist.map get_block := by
  obtain ⟨log, hr, hlog⟩ := run_simTable Sch i pk ω sk c.hist l
  refine ⟨log, ?_, hlog⟩
  rw [simAdv, OracleAdv.run_bind, hr, PMF.pure_bind, OracleAdv.run_ret, simPub_eq i pk ω sk]
  unfold advRaw
  cases c.msgs <;> rfl

end Correct

/-- The blocks of the history of a state. -/
def hb {ω : Seed Tx Hash np n Hz PK SK} (M : GS P ω A) : List (Block Tx Hash (Fin np)) :=
  letI := ω.params P; letI := ω.bparams P
  M.history.map get_block

/-- A party step of the real execution. -/
def sStep (bake : Bool) : Fin np → GS P ω A → GS P ω A :=
  if bake then sBake Sch P ω A false else sRcv Sch P ω A false

/-- The adversary call of a party step. -/
def stepCall (bake : Bool) (p : Fin np) (M : GS P ω A) : CallInput Tx Hash np A.AdvState :=
  if bake then bakeCall P ω A M else rcvCall P ω A p M

/-- The step of a corrupt party in the simulation, given the output `r` of the adversary. -/
def corruptStep (bake : Bool) (p : Fin np) (M : GS P ω A)
    (r : AdvOut Tx Hash np Sig × A.AdvState) : GS P ω A :=
  letI := ω.params P; letI := ω.bparams P
  if bake then
    { flood_msgs_adv (outFilter Sch false (simPks i pk ω) M.t_now M.history r.1) M with
      adv_state := r.2 }
  else
    { flood_msgs_adv (outFilter Sch false (simPks i pk ω) (fetch_msgs p M).2.t_now
        (fetch_msgs p M).2.history r.1) (fetch_msgs p M).2 with adv_state := r.2 }

/-- The programs of the forger: adaptive oracle adversaries with signing queries on blocks that
output a candidate forgery. The simulation passes the simulated state to a continuation of
this type. -/
abbrev FProg (Tx Hash : Type) (np : ℕ) (Sig : Type) :=
  OracleAdv (Block Tx Hash (Fin np)) Sig (Block Tx Hash (Fin np) × Sig)

/-- A party step in the simulation, continued by `k` on the next state: for a corrupt party,
run the adversary with the simulated signatures and stop with the first forgery of party
`i`. -/
def simStep (bake : Bool) (p : Fin np) (M : GS P ω A) (k : GS P ω A → FProg Tx Hash np Sig) :
    FProg Tx Hash np Sig :=
  letI := ω.params P; letI := ω.bparams P
  if (M.state_map p).isSome && is_corrupt p then
    (simAdv Sch A i pk ω (stepCall P A ω bake p M)).bind fun r =>
      match findForgery Sch i (simPks i pk ω) (stepCall P A ω bake p M) r.1 with
      | some fg => .ret fg
      | none => k (corruptStep Sch P A i pk ω bake p M r)
  else k (sStep Sch P A ω bake p M)

/-- The steps of a list of parties in the simulation, in the order of `List.foldr`, continued
by `k` on the final state. -/
def simFold (bake : Bool) (N : GS P ω A) :
    List (Fin np) → (GS P ω A → FProg Tx Hash np Sig) → FProg Tx Hash np Sig
  | [], k => k N
  | p :: ps, k => simFold bake N ps fun M => simStep Sch P A i pk ω bake p M k

/-- One phase in the simulation, continued by `k` on the next state. -/
def simPhase (N : GS P ω A) (k : GS P ω A → FProg Tx Hash np Sig) : FProg Tx Hash np Sig :=
  letI := ω.params P; letI := ω.bparams P
  match N.progress with
  | .Ready => simFold Sch P A i pk ω false N N.exec_order fun M =>
      k { M with progress := .Delivered }
  | .Delivered => simFold Sch P A i pk ω true N N.exec_order fun M =>
      k { M with progress := .Baked }
  | .Baked => k { inc_round (round_tick N) with progress := .Ready }

/-- The first `j` phases in the simulation, continued by `k` on the state after them. -/
def simTrace : ℕ → (GS P ω A → FProg Tx Hash np Sig) → FProg Tx Hash np Sig
  | 0, k => k (sTrace Sch P ω A false 0)
  | j + 1, k => simTrace j fun M => simPhase Sch P A i pk ω M k

/-- **The forger's program.** With verification key `pk` and seed `ω`, simulate the first `K`
phases of the real execution with key `pk` for party `i`, and output the first forgery of
party `i`; without a forgery, query the genesis block and output it with its signature. -/
def forgerProg (K : ℕ) : FProg Tx Hash np Sig :=
  simTrace Sch P A i pk ω K fun _ => .query P.GB fun σ => .ret (P.GB, σ)

section SimCorrect

variable (sk : SK)

theorem sStep_noncall (bake : Bool) (p : Fin np) (M : GS P ω A)
    (h : (letI := ω.params P; letI := ω.bparams P
      (M.state_map p).isSome && is_corrupt p) = false) :
    sStep Sch P A ω bake p M = sStep Sch P A (ω.withKey i (pk, sk)) bake p M := by
  let _ := ω.params P; let _ := ω.bparams P
  cases bake
  · simp only [sStep, sRcv, Bool.false_eq_true, if_false]
    unfold party_rcv_step_world
    cases hs : M.state_map p with
    | none => rfl
    | some l =>
      have hc : is_corrupt p = false := by simpa [hs] using h
      simp only [hc]
      rfl
  · simp only [sStep, sBake, if_true]
    unfold party_bake_step_world
    cases hs : M.state_map p with
    | none => rfl
    | some l =>
      have hc : is_corrupt p = false := by simpa [hs] using h
      simp only [hc]
      rfl

theorem corruptStep_eq (bake : Bool) (p : Fin np) (M : GS P ω A)
    (h : (letI := ω.params P; letI := ω.bparams P
      (M.state_map p).isSome && is_corrupt p) = true) :
    corruptStep Sch P A i pk ω bake p M
        (advRaw Sch (ω.withKey i (pk, sk)) A (stepCall P A ω bake p M)) =
      sStep Sch P A (ω.withKey i (pk, sk)) bake p M := by
  let _ := ω.params P; let _ := ω.bparams P
  simp only [Bool.and_eq_true, Option.isSome_iff_exists] at h
  obtain ⟨⟨l, hl⟩, hc⟩ := h
  cases bake
  · simp only [corruptStep, sStep, sRcv, stepCall, Bool.false_eq_true, if_false]
    unfold party_rcv_step_world
    rw [hl]
    simp only [hc, Bool.not_true, Bool.false_eq_true, if_false]
    rw [mkExec_rcv, simPks_eq i pk ω sk]
    rfl
  · simp only [corruptStep, sStep, sBake, stepCall, if_true]
    unfold party_bake_step_world
    rw [hl]
    simp only [hc, Bool.not_true, Bool.false_eq_true, if_false]
    rw [mkExec_bake, simPks_eq i pk ω sk]
    rfl

theorem hb_sStep (bake : Bool) (p : Fin np) (M : GS P ω A) :
    ∀ b ∈ hb P A M, b ∈ hb P A (sStep Sch P A ω bake p M) := by
  let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec Sch false P ω A
  intro b hb'
  simp only [hb, List.mem_map] at hb' ⊢
  obtain ⟨m, hm, rfl⟩ := hb'
  refine ⟨m, ?_, rfl⟩
  cases bake
  · exact rcv_history_mono M p m hm
  · exact bake_history_mono M p m hm

/-- The specification of a simulated computation `prog` with a continuation, from the state
`Nin`, that should compute the real state `Nout` through the adversary calls `calls`. Run
`prog k` against the signing oracle of `sk` from a list of queries whose blocks lie in the
history of `Nin`. If no call forges a block of party `i`, every outcome is an outcome of
`k Nout` run from a list of queries whose blocks lie in the history of `Nout`; otherwise every
outcome is a block with a valid signature under `pk` that is neither in the history of `Nin`
nor queried. -/
def SimSpec (prog : (GS P ω A → FProg Tx Hash np Sig) → FProg Tx Hash np Sig)
    (calls : List (CallInput Tx Hash np A.AdvState)) (Nin Nout : GS P ω A) : Prop :=
  ∀ (k : GS P ω A → FProg Tx Hash np Sig) (l : List (Block Tx Hash (Fin np) × Sig)),
    (∀ b ∈ l.map Prod.fst, b ∈ hb P A Nin) →
    ∀ x ∈ (OracleAdv.run (signOracle Sch sk) (prog k) l).support,
      ((∀ c ∈ calls, ¬ForgedBy Sch (ω.withKey i (pk, sk)) A i c) →
          ∃ l' : List (Block Tx Hash (Fin np) × Sig), (∀ b ∈ l'.map Prod.fst, b ∈ hb P A Nout) ∧
            x ∈ (OracleAdv.run (signOracle Sch sk) (k Nout) l').support) ∧
        ((∃ c ∈ calls, ForgedBy Sch (ω.withKey i (pk, sk)) A i c) →
          Sch.verify pk x.1.1 x.1.2 = true ∧ x.1.1 ∉ hb P A Nin ∧ x.1.1 ∉ x.2.map Prod.fst)

theorem run_simStep (bake : Bool) (p : Fin np) (M : GS P ω A) :
    SimSpec Sch P A i pk ω sk (simStep Sch P A i pk ω bake p M)
      (stepCalls P (ω.withKey i (pk, sk)) A bake (p, M)) M
      (sStep Sch P A (ω.withKey i (pk, sk)) bake p M) := by
  let _ := ω.params P; let _ := ω.bparams P
  have hhist : (stepCall P A ω bake p M).hist = M.history := by
    cases bake <;> rfl
  intro k l hl x hx
  cases h : ((M.state_map p).isSome && is_corrupt p)
  · have hcalls : stepCalls P (ω.withKey i (pk, sk)) A bake (p, M) = [] := by
      simp only [stepCalls]
      split_ifs with hh
      · exact absurd (h.symm.trans hh) (by decide)
      · rfl
    rw [hcalls]
    simp only [simStep, h, Bool.false_eq_true, if_false] at hx
    refine ⟨fun _ => ⟨l, fun b hb' => hb_sStep Sch P A (ω.withKey i (pk, sk)) bake p M b (hl b hb'),
      ?_⟩, ?_⟩
    · rw [← sStep_noncall Sch P A i pk ω sk bake p M h]
      exact hx
    · rintro ⟨c, hc, _⟩; simp at hc
  · have hcalls : stepCalls P (ω.withKey i (pk, sk)) A bake (p, M) =
        [stepCall P A ω bake p M] := by
      cases bake <;>
      · simp only [stepCalls, stepCall, Bool.false_eq_true, if_false, if_true]
        split_ifs with hh
        · rfl
        · exact absurd h hh
    rw [hcalls]
    obtain ⟨log, hr, hlog⟩ := run_simAdv Sch A i pk ω sk (stepCall P A ω bake p M) l
    simp only [simStep, h, if_true, OracleAdv.run_bind, hr, PMF.pure_bind] at hx
    have hl' : ∀ b ∈ l.map Prod.fst, b ∈ (stepCall P A ω bake p M).hist.map get_block := by
      rw [hhist]; exact hl
    by_cases hF : ForgedBy Sch (ω.withKey i (pk, sk)) A i (stepCall P A ω bake p M)
    · have hF' := hF
      rw [ForgedBy, ← simPks_eq i pk ω sk] at hF'
      obtain ⟨m, σ, hfs⟩ := findForgery_isSome Sch hF'
      rw [hfs] at hx
      simp only [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hx
      subst hx
      obtain ⟨hv, hm⟩ := findForgery_some Sch hfs
      refine ⟨fun hcl => absurd hF (hcl _ (List.mem_singleton_self _)), fun _ => ⟨?_, ?_, ?_⟩⟩
      · simpa [simPks] using hv
      · simpa [hb, hhist] using hm
      · intro hm'
        simp only [List.map_append, List.mem_append] at hm'
        rcases hm' with hm' | hm'
        · exact hm (hl' m hm')
        · exact hm (hlog m hm')
    · have hfn : findForgery Sch i (simPks i pk ω) (stepCall P A ω bake p M)
          (advRaw Sch (ω.withKey i (pk, sk)) A (stepCall P A ω bake p M)).1 = none := by
        refine findForgery_eq_none Sch ?_
        rw [simPks_eq i pk ω sk]
        exact hF
      rw [hfn] at hx
      refine ⟨fun _ => ⟨l ++ log, ?_, ?_⟩,
        fun ⟨c, hc, hc'⟩ => absurd (List.mem_singleton.1 hc ▸ hc') hF⟩
      · intro b hb'
        refine hb_sStep Sch P A (ω.withKey i (pk, sk)) bake p M b ?_
        simp only [List.map_append, List.mem_append] at hb'
        rcases hb' with hb' | hb'
        · exact hl b hb'
        · simpa [hb, hhist] using hlog b hb'
      · rw [← corruptStep_eq Sch P A i pk ω sk bake p M h]
        exact hx

theorem SimSpec.congr_calls
    {prog : (GS P ω A → FProg Tx Hash np Sig) → FProg Tx Hash np Sig}
    {calls calls' : List (CallInput Tx Hash np A.AdvState)}
    {Nin Nout : GS P ω A} (h : SimSpec Sch P A i pk ω sk prog calls Nin Nout)
    (hc : ∀ c, c ∈ calls ↔ c ∈ calls') : SimSpec Sch P A i pk ω sk prog calls' Nin Nout :=
  fun k l hl x hx => ⟨fun hcl => (h k l hl x hx).1 fun c hc' => hcl c ((hc c).1 hc'),
    fun ⟨c, hc', hf⟩ => (h k l hl x hx).2 ⟨c, (hc c).2 hc', hf⟩⟩

/-- Sequential composition of simulated computations: `prog1` continued by `prog2` on the
state it reaches. -/
theorem SimSpec.bind
    {prog1 : (GS P ω A → FProg Tx Hash np Sig) → FProg Tx Hash np Sig}
    {prog2 : GS P ω A → (GS P ω A → FProg Tx Hash np Sig) → FProg Tx Hash np Sig}
    {calls1 calls2 : List (CallInput Tx Hash np A.AdvState)} {N0 N1 N2 : GS P ω A}
    (h1 : SimSpec Sch P A i pk ω sk prog1 calls1 N0 N1)
    (h2 : SimSpec Sch P A i pk ω sk (prog2 N1) calls2 N1 N2)
    (hm01 : ∀ b ∈ hb P A N0, b ∈ hb P A N1) :
    SimSpec Sch P A i pk ω sk (fun k => prog1 fun M => prog2 M k) (calls1 ++ calls2) N0 N2 := by
  intro k l hl x hx
  have hx1 := h1 (fun M => prog2 M k) l hl x hx
  by_cases hf1 : ∃ c ∈ calls1, ForgedBy Sch (ω.withKey i (pk, sk)) A i c
  · refine ⟨fun hcl => ?_, fun _ => hx1.2 hf1⟩
    obtain ⟨c, hc, hc'⟩ := hf1
    exact absurd hc' (hcl c (List.mem_append_left _ hc))
  · have hf1' : ∀ c ∈ calls1, ¬ForgedBy Sch (ω.withKey i (pk, sk)) A i c :=
      fun c hc hc' => hf1 ⟨c, hc, hc'⟩
    obtain ⟨l', hl', hx'⟩ := hx1.1 hf1'
    have hx2 := h2 k l' hl' x hx'
    refine ⟨fun hcl => hx2.1 fun c hc => hcl c (List.mem_append_right _ hc), fun hf => ?_⟩
    have hf2 : ∃ c ∈ calls2, ForgedBy Sch (ω.withKey i (pk, sk)) A i c := by
      obtain ⟨c, hc, hc'⟩ := hf
      rcases List.mem_append.1 hc with hc | hc
      · exact absurd hc' (hf1' c hc)
      · exact ⟨c, hc, hc'⟩
    obtain ⟨hv, hn1, hnl2⟩ := hx2.2 hf2
    exact ⟨hv, fun h => hn1 (hm01 _ h), hnl2⟩

theorem hb_foldr (bake : Bool) (N : GS P ω A) (l : List (Fin np)) :
    ∀ b ∈ hb P A N, b ∈ hb P A (l.foldr (sStep Sch P A ω bake) N) := by
  induction l with
  | nil => exact fun b h => h
  | cons p ps ih => exact fun b h => hb_sStep Sch P A ω bake p _ b (ih b h)

theorem run_simFold (bake : Bool) (N : GS P ω A) (l : List (Fin np)) :
    SimSpec Sch P A i pk ω sk (simFold Sch P A i pk ω bake N l)
      ((foldrCalls (sStep Sch P A (ω.withKey i (pk, sk)) bake) N l).flatMap
        (stepCalls P (ω.withKey i (pk, sk)) A bake)) N
      (l.foldr (sStep Sch P A (ω.withKey i (pk, sk)) bake) N) := by
  induction l with
  | nil =>
    intro k lg hl x hx
    refine ⟨fun _ => ⟨lg, hl, hx⟩, ?_⟩
    rintro ⟨c, hc, _⟩; simp [foldrCalls] at hc
  | cons p ps ih =>
    have h := SimSpec.bind Sch P A i pk ω sk (prog2 := fun M => simStep Sch P A i pk ω bake p M) ih
      (run_simStep Sch P A i pk ω sk bake p (ps.foldr (sStep Sch P A (ω.withKey i (pk, sk)) bake) N))
      (hb_foldr Sch P A (ω.withKey i (pk, sk)) bake N ps)
    refine SimSpec.congr_calls Sch P A i pk ω sk h fun c => ?_
    simp only [foldrCalls, List.flatMap_cons, List.mem_append]
    exact or_comm

theorem hb_sPhase (N : GS P ω A) : ∀ b ∈ hb P A N, b ∈ hb P A (sPhase Sch P ω A false N) := by
  intro b h
  rw [sPhase_def]
  let _ := ω.params P; let _ := ω.bparams P
  cases N.progress with
  | Ready => exact hb_foldr Sch P A ω false N N.exec_order b h
  | Delivered => exact hb_foldr Sch P A ω true N N.exec_order b h
  | Baked => exact h

theorem run_simPhase (N : GS P ω A) :
    SimSpec Sch P A i pk ω sk (simPhase Sch P A i pk ω N)
      (phaseCalls Sch P (ω.withKey i (pk, sk)) A N) N
      (sPhase Sch P (ω.withKey i (pk, sk)) A false N) := by
  let _ := ω.params P; let _ := ω.bparams P
  rw [sPhase_def]
  unfold simPhase phaseCalls
  cases hp : N.progress with
  | Ready =>
    dsimp only
    intro k lg hl x hx
    exact run_simFold Sch P A i pk ω sk false N N.exec_order _ lg hl x hx
  | Delivered =>
    dsimp only
    intro k lg hl x hx
    exact run_simFold Sch P A i pk ω sk true N N.exec_order _ lg hl x hx
  | Baked =>
    dsimp only
    intro k lg hl x hx
    refine ⟨fun _ => ⟨lg, hl, hx⟩, ?_⟩
    rintro ⟨c, hc, _⟩; simp at hc

theorem traceCalls_succ (ω : Seed Tx Hash np n Hz PK SK) (k : ℕ) :
    traceCalls Sch P ω A (k + 1) =
      traceCalls Sch P ω A k ++ phaseCalls Sch P ω A (sTrace Sch P ω A false k) := by
  simp [traceCalls, List.range_succ, List.flatMap_append]

theorem run_simTrace (j : ℕ) :
    SimSpec Sch P A i pk ω sk (simTrace Sch P A i pk ω j)
      (traceCalls Sch P (ω.withKey i (pk, sk)) A j) (sTrace Sch P ω A false 0)
      (sTrace Sch P (ω.withKey i (pk, sk)) A false j) := by
  induction j with
  | zero =>
    intro k lg hl x hx
    refine ⟨fun _ => ⟨lg, hl, hx⟩, ?_⟩
    rintro ⟨c, hc, _⟩; simp [traceCalls] at hc
  | succ j ih =>
    have h := SimSpec.bind Sch P A i pk ω sk (prog2 := simPhase Sch P A i pk ω) ih
      (run_simPhase Sch P A i pk ω sk _)
      (fun b hb' => by
        let _ := ω.params P; let _ := ω.bparams P
        simp [hb, sTrace, runTrace, N0] at hb')
    rw [traceCalls_succ, sTrace_succ]
    exact h

/-- **The forger wins on a forgery.** If the adversary forges a block of party `i` in the
first `K` phases of the real execution for the seed `ω` with the key pair `(pk, sk)` for party
`i`, every outcome of the forger's program with verification key `pk` and seed `ω` against the
signing oracle of `sk` is a message with a valid signature that it did not query. -/
theorem forgerProg_wins (K : ℕ) (h : ForgeBy Sch P (ω.withKey i (pk, sk)) A K i) :
    ∀ x ∈ (OracleAdv.run (signOracle Sch sk) (forgerProg Sch P A i pk ω K) []).support,
      (Sch.verify pk x.1.1 x.1.2 && !(x.2.map Prod.fst).contains x.1.1) = true := by
  intro x hx
  obtain ⟨hv, -, hnl⟩ := (run_simTrace Sch P A i pk ω sk K _ [] (by simp) x hx).2 h
  simpa [hv] using hnl

/-- **The forger loses without a forgery.** If no adversary call of the first `K` phases of the
real execution for the seed `ω` with the key pair `(pk, sk)` for party `i` forges a block of
party `i`, every outcome of the forger's program outputs a queried message. -/
theorem forgerProg_loses (K : ℕ)
    (h : ∀ c ∈ traceCalls Sch P (ω.withKey i (pk, sk)) A K,
      ¬ForgedBy Sch (ω.withKey i (pk, sk)) A i c) :
    ∀ x ∈ (OracleAdv.run (signOracle Sch sk) (forgerProg Sch P A i pk ω K) []).support,
      (Sch.verify pk x.1.1 x.1.2 && !(x.2.map Prod.fst).contains x.1.1) = false := by
  intro x hx
  obtain ⟨l', -, hx'⟩ := (run_simTrace Sch P A i pk ω sk K _ [] (by simp) x hx).1 h
  simp only [run_query_signOracle_det, OracleAdv.run_ret, PMF.support_pure,
    Set.mem_singleton_iff] at hx'
  subst hx'
  simp

end SimCorrect

end Forger

/-! ## The probability of a forgery -/

/-- Replacing one coordinate of independent identically distributed draws by a fresh draw does
not change the distribution. -/
theorem piFin_update {α : Type} (d : PMF α) : ∀ {m : ℕ} (i : Fin m),
    (PMF.piFin fun _ : Fin m => d).bind (fun v => d.bind fun a => PMF.pure (Function.update v i a)) =
      PMF.piFin fun _ : Fin m => d
  | 0, i => i.elim0
  | m + 1, i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [PMF.piFin, PMF.bind_bind, PMF.pure_bind, Fin.update_cons_zero]
      rw [PMF.bind_const]
      exact PMF.bind_comm _ _ _
    · simp only [PMF.piFin, PMF.bind_bind, PMF.pure_bind, ← Fin.cons_update]
      rw [show (Fin.tail fun _ : Fin (m + 1) => d) = fun _ : Fin m => d from rfl]
      congr 1
      funext a
      conv_rhs => rw [← piFin_update d j]
      simp only [PMF.bind_bind, PMF.pure_bind]

/-- An event of a double bind whose branch probabilities are bounded by the branch
probabilities of another event of a double bind over the same two distributions has a bounded
probability. -/
theorem toOuterMeasure_bind_bind_le {α β γ δ : Type} (p : PMF α) (q : PMF β)
    (f : α → β → PMF γ) (g : α → β → PMF δ) (S : Set γ) (T : Set δ)
    (h : ∀ a b, (f a b).toOuterMeasure S ≤ (g a b).toOuterMeasure T) :
    (p.bind fun a => q.bind (f a)).toOuterMeasure S ≤
      (p.bind fun a => q.bind (g a)).toOuterMeasure T := by
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  refine ENNReal.tsum_le_tsum fun a => ?_
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  gcongr with b
  exact h a b

section Prob

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ} {PK SK Sig : Type}
  (Sch : PSigScheme (Block Tx Hash (Fin np)) PK SK Sig) [hS : Sch.Deterministic]

/-- The distribution of the random seed for the keyed hash family `H` with the codec `cd` of
the block domain: the slot leaders (`leaderDist μ h0 W n`), a uniformly random key `k` with the
hash function `cd.hashOn k`, and independent key pairs from `Sch.keyDist`, all independent.
For `H = HashScheme.randomFun` and the identity codec, the hash function is a uniformly random
function. -/
noncomputable def seedDist (H : HashScheme) (cd : H.Codec (BlockDom Tx Hash np Hz) Hash)
    (μ : PMF (Option (Fin np))) (h0 : Fin np) (W n : ℕ) : PMF (Seed Tx Hash np n Hz PK SK) :=
  (leaderDist μ h0 W n).bind fun L => (PMF.uniformOfFintype H.Key).bind fun k =>
    (PMF.piFin fun _ => Sch.keyDist).bind fun ks => PMF.pure ⟨L, cd.hashOn k, ks⟩

theorem seedDist_withKey (H : HashScheme) (cd : H.Codec (BlockDom Tx Hash np Hz) Hash)
    (μ : PMF (Option (Fin np))) (h0 : Fin np) (W : ℕ) (i : Fin np) :
    (seedDist Sch H cd μ h0 W n).bind
        (fun ω => Sch.keyDist.bind fun kp => PMF.pure (ω.withKey i kp)) =
      seedDist Sch H cd μ h0 W n := by
  simp only [seedDist, PMF.bind_bind, PMF.pure_bind]
  congr 1; funext L; congr 1; funext k
  conv_rhs => rw [← piFin_update Sch.keyDist i]
  simp only [PMF.bind_bind, PMF.pure_bind]

variable (P : Protocol Tx Hash np n Hz) (A : Adversary Tx Hash np n Hz PK Sig)

/-- **The reduction.** The EUF-CMA adversary obtained from the adversary `A` against the signed
protocol, the keyed hash family `H` with codec `cd` and the party `i`: on the verification key
`pk` it draws a seed from `seedDist Sch H cd` and runs `forgerProg`, which simulates the first
`K` phases of the real execution with the key `pk` for party `i` and outputs the first forgery
of party `i`. -/
noncomputable def forger (H : HashScheme) (cd : H.Codec (BlockDom Tx Hash np Hz) Hash)
    (μ : PMF (Option (Fin np))) (W K : ℕ) (i : Fin np) (pk : PK) :
    OracleAdv (Block Tx Hash (Fin np)) Sig (Block Tx Hash (Fin np) × Sig) :=
  .rand (seedDist Sch H cd μ P.h0 W n) fun ω => forgerProg Sch P A i pk ω K

/-- **Forging a block of party `i` (part 3).** Over the seed distribution `seedDist Sch H cd`,
the probability that the adversary `A` forges a block of party `i` in the first `K` phases of
the real execution is at most the EUF-CMA advantage of the explicit adversary
`toEUFAdversary (forger Sch P A H cd μ W K i)` against `Sch`. -/
theorem prob_forgeBy_le (H : HashScheme) (cd : H.Codec (BlockDom Tx Hash np Hz) Hash)
    (μ : PMF (Option (Fin np))) (W K : ℕ) (i : Fin np) :
    (seedDist Sch H cd μ P.h0 W n).toOuterMeasure {ω | ForgeBy Sch P ω A K i} ≤
      eufcmaAdvantage Sch.toSigScheme (toEUFAdversary (forger Sch P A H cd μ W K i)) := by
  have hseed := seedDist_withKey (n := n) Sch H cd μ P.h0 W i
  rw [PMF.bind_comm, PSigScheme.keyDist, PMF.bind_map] at hseed
  rw [eufcmaAdvantage_toEUFAdversary, eufDist, ← PMF.toOuterMeasure_apply_singleton]
  conv_lhs => rw [← hseed]
  simp only [forger, OracleAdv.run_rand, PMF.map_bind]
  refine toOuterMeasure_bind_bind_le _ _ _ _ _ _ fun kr ω => ?_
  rw [PMF.toOuterMeasure_pure_apply]
  split_ifs with hF
  · refine le_of_eq ((PMF.toOuterMeasure_apply_eq_one_iff _ _).2 ?_).symm
    rw [PMF.support_map]
    rintro _ ⟨x, hx, rfl⟩
    exact forgerProg_wins Sch P A i (Sch.keygen kr).1 ω (Sch.keygen kr).2 K hF x hx
  · exact bot_le

/-- **Forging an honest block.** Over the seed distribution `seedDist Sch H cd`, the probability
that the adversary forges an honest block in the first `K` phases of the real execution is at
most the sum over the parties `i` of the EUF-CMA advantages of the explicit adversaries
`toEUFAdversary (forger Sch P A H cd μ W K i)`. -/
theorem prob_forge_le (H : HashScheme) (cd : H.Codec (BlockDom Tx Hash np Hz) Hash)
    (μ : PMF (Option (Fin np))) (W K : ℕ) :
    (seedDist Sch H cd μ P.h0 W n).toOuterMeasure {ω | Forge Sch P ω A K} ≤
      ∑ i : Fin np,
        eufcmaAdvantage Sch.toSigScheme (toEUFAdversary (forger Sch P A H cd μ W K i)) := by
  have hsub : {ω | Forge Sch P ω A K} ⊆ ⋃ i ∈ (Finset.univ : Finset (Fin np)),
      {ω | ForgeBy Sch P ω A K i} := by
    intro ω hω
    obtain ⟨i, hi⟩ := forge_iff_exists Sch P ω A K hω
    simp only [Set.mem_iUnion]
    exact ⟨i, Finset.mem_univ _, hi⟩
  refine (MeasureTheory.OuterMeasure.mono _ hsub).trans ?_
  refine (MeasureTheory.measure_biUnion_finset_le
    (μ := (seedDist Sch H cd μ P.h0 W n).toOuterMeasure) _ _).trans ?_
  exact Finset.sum_le_sum fun i _ => prob_forgeBy_le Sch P A H cd μ W K i

end Prob

end CatCryptCore.Consensus.PoSNSB
