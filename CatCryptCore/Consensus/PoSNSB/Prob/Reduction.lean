/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.PoSNSB.Prob.Protocol

/-!
# PoS-NSB: forging honest blocks reduces to EUF-CMA

This file defines the existential unforgeability game under chosen-message attacks (EUF-CMA) of
a signature scheme and, for every adversary `A` against the signed protocol of
`CatCryptCore/Consensus/PoSNSB/Prob/Protocol.lean` and every party `i`, an explicit adversary
`forger A i` against EUF-CMA. The forger receives the verification key of the game and a
signing oracle, samples the lottery, the random oracle and the key pairs of the other parties
itself, runs the real execution with the key of the game for party `i`, obtains the signatures
of the honest blocks of party `i` from the signing oracle, and outputs the first accepted block
of party `i` that the adversary sends outside the history.

## Main definitions

* `OracleProg Msg Sig α`: programs with access to a signing oracle; `OracleProg.run` runs a
  program against a signing function and returns its result and the list of queried messages.
* `EUFAdversary`, `eufGame`, `eufAdv`: the EUF-CMA game and the advantage. The adversary wins
  when it outputs a message with a valid signature that it did not query.
* `seedDist`: the distribution of the random seed, `ForgeBy`: the adversary of the real
  execution forges a block of party `i`.
* `forger A i`: the reduction.

## Main results

* `forger_wins`: if the adversary forges a block of party `i` in the real execution for the
  seed `ω` with the key pair `kp` for party `i`, the forger wins the EUF-CMA game with key pair
  `kp` and coins `ω`.
* `prob_forgeBy_le`: `Pr[ForgeBy i] ≤ eufAdv (forger A i)`.
* `prob_forge_le`: `Pr[Forge] ≤ ∑ᵢ eufAdv (forger A i)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace CatCryptCore.Consensus.PoSNSB

universe u v

open Parameters BlockParameters Corruption Execution
open scoped ENNReal

/-! ## Oracle programs and the EUF-CMA game -/

/-- A program with access to a signing oracle on messages `Msg` with signatures `Sig`. -/
inductive OracleProg (Msg Sig : Type) (α : Type u) : Type u where
  /-- Return a result. -/
  | ret : α → OracleProg Msg Sig α
  /-- Ask the oracle for the signature of a message and continue with the answer. -/
  | query : Msg → (Sig → OracleProg Msg Sig α) → OracleProg Msg Sig α

namespace OracleProg

variable {Msg Sig : Type} {α : Type u} {β : Type v}

/-- Sequential composition of oracle programs. -/
def bind : OracleProg Msg Sig α → (α → OracleProg Msg Sig β) → OracleProg Msg Sig β
  | ret a, g => g a
  | query m k, g => query m fun s => bind (k s) g

/-- Run a program against the signing function `sg`: its result and the list of queried
messages. -/
def run (sg : Msg → Sig) : OracleProg Msg Sig α → α × List Msg
  | ret a => (a, [])
  | query m k => ((run sg (k (sg m))).1, m :: (run sg (k (sg m))).2)

theorem run_bind (sg : Msg → Sig) (p : OracleProg Msg Sig α) (g : α → OracleProg Msg Sig β) :
    run sg (bind p g) = ((run sg (g (run sg p).1)).1, (run sg p).2 ++ (run sg (g (run sg p).1)).2) := by
  induction p with
  | ret a => simp [bind, run]
  | query m k ih => simp [bind, run, ih]

@[simp] theorem run_ret (sg : Msg → Sig) (a : α) : run sg (ret a : OracleProg Msg Sig α) = (a, []) :=
  rfl

end OracleProg

/-- An adversary against EUF-CMA: coins drawn from a distribution, and an oracle program that
receives the verification key and the coins and outputs a candidate forgery. -/
structure EUFAdversary {Msg : Type} (Sch : SigScheme Msg) where
  /-- The coins of the adversary. -/
  Coins : Type
  /-- The distribution of the coins. -/
  coins : PMF Coins
  /-- The program. -/
  forge : Sch.PK → Coins → OracleProg Msg Sch.Sig (Option (Msg × Sch.Sig))

/-- The adversary wins with key pair `kp` and coins `c`: it outputs a message with a valid
signature that it did not query. -/
def eufWins {Msg : Type} [DecidableEq Msg] {Sch : SigScheme Msg} (B : EUFAdversary Sch)
    (kp : Sch.PK × Sch.SK) (c : B.Coins) : Bool :=
  match (OracleProg.run (Sch.sign kp.2) (B.forge kp.1 c)).1 with
  | some (m, σ) => Sch.verify kp.1 m σ && !(OracleProg.run (Sch.sign kp.2) (B.forge kp.1 c)).2.contains m
  | none => false

/-- The joint distribution of the key pair and the coins in the EUF-CMA game. -/
noncomputable def eufInputs {Msg : Type} {Sch : SigScheme Msg} (B : EUFAdversary Sch) :
    PMF ((Sch.PK × Sch.SK) × B.Coins) :=
  Sch.keygen.bind fun kp => B.coins.bind fun c => PMF.pure (kp, c)

/-- The EUF-CMA game: generate a key pair, draw the coins, run the adversary with the signing
oracle, and output whether it wins. -/
noncomputable def eufGame {Msg : Type} [DecidableEq Msg] {Sch : SigScheme Msg}
    (B : EUFAdversary Sch) : PMF Bool :=
  (eufInputs B).map fun x => eufWins B x.1 x.2

/-- The EUF-CMA advantage: the probability that the adversary wins. -/
noncomputable def eufAdv {Msg : Type} [DecidableEq Msg] {Sch : SigScheme Msg}
    (B : EUFAdversary Sch) : ℝ≥0∞ :=
  eufGame B true

theorem eufAdv_eq {Msg : Type} [DecidableEq Msg] {Sch : SigScheme Msg} (B : EUFAdversary Sch) :
    eufAdv B = (eufInputs B).toOuterMeasure {x | eufWins B x.1 x.2 = true} := by
  rw [eufAdv, eufGame, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  rfl


/-! ## The forger -/

section Forger

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ} {Sch : SigScheme (Block Tx Hash (Fin np))}

open OracleProg

/-- The seed `ω` with the key pair `kp` for party `i`. -/
abbrev Seed.withKey (ω : Seed Tx Hash np n Hz Sch) (i : Fin np) (kp : Sch.PK × Sch.SK) :
    Seed Tx Hash np n Hz Sch :=
  { ω with ks := Function.update ω.ks i kp }

/-- The adversary call `c` forges a block of party `i`: it outputs an accepted honest block of
party `i` that is not in the history. -/
def ForgedBy (ω : Seed Tx Hash np n Hz Sch) (A : Adversary Tx Hash np n Hz Sch) (i : Fin np)
    (c : CallInput Tx Hash np A.AdvState) : Prop :=
  ∃ x ∈ (advRaw ω A c).1, sigOK (fun j => (ω.ks j).1) c.sl x = true ∧ histOK c.hist x = false ∧
    (get_block x.1.1).bid = i

/-- **The forging event for party `i`.** Some adversary call in the first `K` phases of the real
execution forges a block of party `i`. -/
def ForgeBy (P : Protocol Tx Hash np) (ω : Seed Tx Hash np n Hz Sch)
    (A : Adversary Tx Hash np n Hz Sch) (K : ℕ) (i : Fin np) : Prop :=
  ∃ c ∈ traceCalls P ω A K, ForgedBy ω A i c

theorem forge_iff_exists (P : Protocol Tx Hash np) (ω : Seed Tx Hash np n Hz Sch)
    (A : Adversary Tx Hash np n Hz Sch) (K : ℕ) :
    Forge P ω A K → ∃ i, ForgeBy P ω A K i := by
  rintro ⟨c, hc, x, hx, h1, h2⟩
  exact ⟨_, c, hc, x, hx, h1, h2, rfl⟩

/-- The first output of party `i` that the network accepts although it is an honest block
outside the history. -/
def findForgery {AdvState : Type} (i : Fin np) (pks : Fin np → Sch.PK)
    (c : CallInput Tx Hash np AdvState) (out : AdvOut Tx Hash np Sch.Sig) :
    Option (Block Tx Hash (Fin np) × Sch.Sig) :=
  (out.find? fun x => sigOK pks c.sl x && !histOK c.hist x && decide ((get_block x.1.1).bid = i)).map
    fun x => (get_block x.1.1, x.1.2)

theorem findForgery_none {AdvState : Type} {i : Fin np} {pks : Fin np → Sch.PK}
    {c : CallInput Tx Hash np AdvState} {out : AdvOut Tx Hash np Sch.Sig}
    (h : findForgery i pks c out = none) :
    ¬∃ x ∈ out, sigOK pks c.sl x = true ∧ histOK c.hist x = false ∧ (get_block x.1.1).bid = i := by
  rintro ⟨x, hx, h1, h2, h3⟩
  simp only [findForgery, Option.map_eq_none_iff, List.find?_eq_none] at h
  have := h x hx
  simp [h1, h2, h3] at this

theorem findForgery_some {AdvState : Type} {i : Fin np} {pks : Fin np → Sch.PK}
    {c : CallInput Tx Hash np AdvState} {out : AdvOut Tx Hash np Sch.Sig}
    {m : Block Tx Hash (Fin np)} {σ : Sch.Sig} (h : findForgery i pks c out = some (m, σ)) :
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

theorem findForgery_isSome {AdvState : Type} {i : Fin np} {pks : Fin np → Sch.PK}
    {c : CallInput Tx Hash np AdvState} {out : AdvOut Tx Hash np Sch.Sig}
    (h : ∃ x ∈ out, sigOK pks c.sl x = true ∧ histOK c.hist x = false ∧ (get_block x.1.1).bid = i) :
    ∃ m σ, findForgery i pks c out = some (m, σ) := by
  cases hf : findForgery i pks c out with
  | none => exact absurd h (findForgery_none hf)
  | some fg => exact ⟨fg.1, fg.2, rfl⟩

theorem findForgery_eq_none {AdvState : Type} {i : Fin np} {pks : Fin np → Sch.PK}
    {c : CallInput Tx Hash np AdvState} {out : AdvOut Tx Hash np Sch.Sig}
    (h : ¬∃ x ∈ out, sigOK pks c.sl x = true ∧ histOK c.hist x = false ∧ (get_block x.1.1).bid = i) :
    findForgery i pks c out = none := by
  simp only [findForgery, Option.map_eq_none_iff, List.find?_eq_none]
  intro x hx hx'
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at hx'
  exact h ⟨x, hx, hx'.1.1, hx'.1.2, hx'.2⟩

variable (P : Protocol Tx Hash np) (A : Adversary Tx Hash np n Hz Sch) (i : Fin np)
  (pk : Sch.PK) (ω : Seed Tx Hash np n Hz Sch)

/-- Oracle programs for the forger. -/
abbrev Prog (α : Type u) := OracleProg (Block Tx Hash (Fin np)) Sch.Sig α

/-- The verification keys of the simulation: `pk` for party `i`, the keys of `ω` for the other
parties. -/
def simPks : Fin np → Sch.PK := fun j => if j = i then pk else (ω.ks j).1

/-- The public information of the simulation. -/
def simPub : PubInfo Tx Hash np n Hz Sch := (ω.κ, ω.f, simPks i pk ω)

/-- The signature of a block in the simulation: from the signing oracle for party `i`, with
the keys of `ω` for the other parties. -/
def simSign (b : Block Tx Hash (Fin np)) : Prog (Sch := Sch) (Block Tx Hash (Fin np) × Sch.Sig) :=
  if b.bid = i then .query b fun σ => .ret (b, σ) else .ret (b, Sch.sign (ω.ks b.bid).2 b)

/-- Apply an oracle program to every element of a list. -/
def mapQ {Msg Sig β : Type} {γ : Type} (g : β → OracleProg Msg Sig γ) :
    List β → OracleProg Msg Sig (List γ)
  | [] => .ret []
  | b :: bs => (g b).bind fun x => (mapQ g bs).bind fun xs => .ret (x :: xs)

theorem run_mapQ {Msg Sig β γ : Type} (sg : Msg → Sig) (g : β → OracleProg Msg Sig γ)
    (l : List β) :
    run sg (mapQ g l) = (l.map fun b => (run sg (g b)).1, l.flatMap fun b => (run sg (g b)).2) := by
  induction l with
  | nil => rfl
  | cons b bs ih => simp [mapQ, run_bind, ih]

/-- The signatures of the honest blocks of a history in the simulation. -/
def simTable (hist : History Tx Hash (Fin np)) :
    Prog (Sch := Sch) (List (Block Tx Hash (Fin np) × Sch.Sig)) :=
  mapQ (simSign i ω) ((hist.map get_block).filter honest_block)

/-- An adversary call in the simulation. -/
def simAdv (c : CallInput Tx Hash np A.AdvState) :
    Prog (Sch := Sch) (AdvOut Tx Hash np Sch.Sig × A.AdvState) :=
  (simTable i ω c.hist).bind fun tbl => .ret (match c.msgs with
    | none => A.bake (simPub i pk ω) c.sl c.hist tbl c.mb c.st
    | some ms => A.rcv (simPub i pk ω) ms c.sl c.hist tbl c.mb c.st)

section Correct

variable (sk : Sch.SK)

theorem simPks_eq : simPks i pk ω = fun j => ((ω.withKey i (pk, sk)).ks j).1 := by
  funext j
  by_cases h : j = i
  · subst h; simp [simPks]
  · simp [simPks, h]

theorem simPub_eq : simPub i pk ω = (ω.withKey i (pk, sk)).pub := by
  simp only [simPub, Seed.pub, simPks_eq i pk ω sk]

theorem run_simTable (hist : History Tx Hash (Fin np)) :
    (run (Sch.sign sk) (simTable i ω hist)).1 = sigTable (ω.withKey i (pk, sk)).ks hist ∧
      ∀ b ∈ (run (Sch.sign sk) (simTable i ω hist)).2, b ∈ hist.map get_block := by
  rw [simTable, run_mapQ]
  constructor
  · simp only [sigTable]
    refine List.map_congr_left fun b _ => ?_
    by_cases h : b.bid = i
    · simp [simSign, h, run]
    · simp [simSign, h]
  · intro b hb
    simp only [List.mem_flatMap] at hb
    obtain ⟨b', hb', hb⟩ := hb
    have hb'' := (List.mem_filter.1 hb').1
    by_cases h : b'.bid = i
    · simp [simSign, h, run] at hb; rw [hb]; exact hb''
    · simp [simSign, h] at hb

theorem run_simAdv (c : CallInput Tx Hash np A.AdvState) :
    (run (Sch.sign sk) (simAdv A i pk ω c)).1 = advRaw (ω.withKey i (pk, sk)) A c ∧
      ∀ b ∈ (run (Sch.sign sk) (simAdv A i pk ω c)).2, b ∈ c.hist.map get_block := by
  obtain ⟨h1, h2⟩ := run_simTable i pk ω sk c.hist
  rw [simAdv, run_bind]
  refine ⟨?_, fun b hb => ?_⟩
  · simp only [run_ret, h1, simPub_eq i pk ω sk, advRaw]
    cases c.msgs <;> rfl
  · simp only [run_ret, List.append_nil] at hb
    exact h2 b hb

end Correct

/-- The blocks of the history of a state. -/
def hb {ω : Seed Tx Hash np n Hz Sch} (M : GS P ω A) : List (Block Tx Hash (Fin np)) :=
  letI := ω.params P; letI := ω.bparams P
  M.history.map get_block

/-- A party step of the real execution. -/
def sStep (bake : Bool) : Fin np → GS P ω A → GS P ω A :=
  if bake then sBake P ω A false else sRcv P ω A false

/-- The adversary call of a party step. -/
def stepCall (bake : Bool) (p : Fin np) (M : GS P ω A) : CallInput Tx Hash np A.AdvState :=
  if bake then bakeCall P ω A M else rcvCall P ω A p M

/-- The step of a corrupt party in the simulation, given the output `r` of the adversary. -/
def corruptStep (bake : Bool) (p : Fin np) (M : GS P ω A)
    (r : AdvOut Tx Hash np Sch.Sig × A.AdvState) : GS P ω A :=
  letI := ω.params P; letI := ω.bparams P
  if bake then
    { flood_msgs_adv (outFilter false (simPks i pk ω) M.t_now M.history r.1) M with adv_state := r.2 }
  else
    { flood_msgs_adv (outFilter false (simPks i pk ω) (fetch_msgs p M).2.t_now
        (fetch_msgs p M).2.history r.1) (fetch_msgs p M).2 with adv_state := r.2 }

/-- A party step in the simulation: for a corrupt party, run the adversary with the simulated
signatures and stop with the first forgery of party `i`. -/
def simStep (bake : Bool) (p : Fin np) (M : GS P ω A) :
    Prog (Sch := Sch) (GS P ω A ⊕ (Block Tx Hash (Fin np) × Sch.Sig)) :=
  letI := ω.params P; letI := ω.bparams P
  if (M.state_map p).isSome && is_corrupt p then
    (simAdv A i pk ω (stepCall P A ω bake p M)).bind fun r =>
      match findForgery i (simPks i pk ω) (stepCall P A ω bake p M) r.1 with
      | some fg => .ret (Sum.inr fg)
      | none => .ret (Sum.inl (corruptStep P A i pk ω bake p M r))
  else .ret (Sum.inl (sStep P A ω bake p M))

/-- The steps of a list of parties in the simulation, in the order of `List.foldr`. -/
def simFold (bake : Bool) (N : GS P ω A) :
    List (Fin np) → Prog (Sch := Sch) (GS P ω A ⊕ (Block Tx Hash (Fin np) × Sch.Sig))
  | [] => .ret (.inl N)
  | p :: ps => (simFold bake N ps).bind fun r => match r with
      | Sum.inl M => simStep P A i pk ω bake p M
      | Sum.inr fg => .ret (Sum.inr fg)

/-- One phase in the simulation. -/
def simPhase (N : GS P ω A) : Prog (Sch := Sch) (GS P ω A ⊕ (Block Tx Hash (Fin np) × Sch.Sig)) :=
  letI := ω.params P; letI := ω.bparams P
  match N.progress with
  | .Ready => (simFold P A i pk ω false N N.exec_order).bind fun r =>
      .ret (r.map (fun M => { M with progress := .Delivered }) id)
  | .Delivered => (simFold P A i pk ω true N N.exec_order).bind fun r =>
      .ret (r.map (fun M => { M with progress := .Baked }) id)
  | .Baked => .ret (.inl { inc_round (round_tick N) with progress := .Ready })

/-- The first `k` phases in the simulation. -/
def simTrace : ℕ → Prog (Sch := Sch) (GS P ω A ⊕ (Block Tx Hash (Fin np) × Sch.Sig))
  | 0 => .ret (Sum.inl (sTrace P ω A false 0))
  | k + 1 => (simTrace k).bind fun r => match r with
      | Sum.inl M => simPhase P A i pk ω M
      | Sum.inr fg => .ret (Sum.inr fg)

/-- **The forger.** With verification key `pk` and coins `ω`, simulate the first `K` phases of
the real execution with key `pk` for party `i`, and output the first forgery of party `i`. -/
def forgerProg (K : ℕ) : Prog (Sch := Sch) (Option (Block Tx Hash (Fin np) × Sch.Sig)) :=
  (simTrace P A i pk ω K).bind fun r => .ret (match r with
    | Sum.inr fg => some fg
    | Sum.inl _ => none)

section SimCorrect

variable (sk : Sch.SK)

theorem sStep_noncall (bake : Bool) (p : Fin np) (M : GS P ω A)
    (h : (letI := ω.params P; letI := ω.bparams P
      (M.state_map p).isSome && is_corrupt p) = false) :
    sStep P A ω bake p M = sStep P A (ω.withKey i (pk, sk)) bake p M := by
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
    corruptStep P A i pk ω bake p M (advRaw (ω.withKey i (pk, sk)) A (stepCall P A ω bake p M)) =
      sStep P A (ω.withKey i (pk, sk)) bake p M := by
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
    ∀ b ∈ hb P A M, b ∈ hb P A (sStep P A ω bake p M) := by
  let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec false P ω A
  intro b hb'
  simp only [hb, List.mem_map] at hb' ⊢
  obtain ⟨m, hm, rfl⟩ := hb'
  refine ⟨m, ?_, rfl⟩
  cases bake
  · exact rcv_history_mono M p m hm
  · exact bake_history_mono M p m hm

/-- The specification of a simulated computation from the state `Nin` that should compute the
real state `Nout` through the adversary calls `calls`: without a forgery of party `i` among the
calls it returns `Nout` and queries only blocks of the history of `Nout`; otherwise it returns
a block with a valid signature under `pk` that is neither in the history of `Nin` nor
queried. -/
def SimSpec (R : (GS P ω A ⊕ (Block Tx Hash (Fin np) × Sch.Sig)) × List (Block Tx Hash (Fin np)))
    (calls : List (CallInput Tx Hash np A.AdvState)) (Nin Nout : GS P ω A) : Prop :=
  ((∀ c ∈ calls, ¬ForgedBy (ω.withKey i (pk, sk)) A i c) →
      R.1 = Sum.inl Nout ∧ ∀ b ∈ R.2, b ∈ hb P A Nout) ∧
    ((∃ c ∈ calls, ForgedBy (ω.withKey i (pk, sk)) A i c) →
      ∃ m σ, R.1 = Sum.inr (m, σ) ∧ Sch.verify pk m σ = true ∧ m ∉ hb P A Nin ∧ m ∉ R.2)

theorem run_simStep (bake : Bool) (p : Fin np) (M : GS P ω A) :
    SimSpec P A i pk ω sk (run (Sch.sign sk) (simStep P A i pk ω bake p M))
      (stepCalls P (ω.withKey i (pk, sk)) A bake (p, M)) M
      (sStep P A (ω.withKey i (pk, sk)) bake p M) := by
  let _ := ω.params P; let _ := ω.bparams P
  have hhist : (stepCall P A ω bake p M).hist = M.history := by
    cases bake <;> rfl
  cases h : ((M.state_map p).isSome && is_corrupt p)
  · have hcalls : stepCalls P (ω.withKey i (pk, sk)) A bake (p, M) = [] := by
      simp only [stepCalls]
      split_ifs with hh
      · exact absurd (h.symm.trans hh) (by decide)
      · rfl
    rw [hcalls]
    simp only [simStep, h, Bool.false_eq_true, if_false, run_ret]
    refine ⟨fun _ => ⟨by rw [sStep_noncall P A i pk ω sk bake p M h], by simp⟩, ?_⟩
    rintro ⟨c, hc, _⟩; simp at hc
  · have hcalls : stepCalls P (ω.withKey i (pk, sk)) A bake (p, M) =
        [stepCall P A ω bake p M] := by
      cases bake <;>
      · simp only [stepCalls, stepCall, Bool.false_eq_true, if_false, if_true]
        split_ifs with hh
        · rfl
        · exact absurd h hh
    rw [hcalls]
    obtain ⟨hr1, hr2⟩ := run_simAdv A i pk ω sk (stepCall P A ω bake p M)
    simp only [simStep, h, if_true, run_bind, hr1]
    by_cases hF : ForgedBy (ω.withKey i (pk, sk)) A i (stepCall P A ω bake p M)
    · have hF' := hF
      rw [ForgedBy, ← simPks_eq i pk ω sk] at hF'
      obtain ⟨m, σ, hfs⟩ := findForgery_isSome hF'
      rw [hfs]
      obtain ⟨hv, hm⟩ := findForgery_some hfs
      refine ⟨fun hcl => absurd hF (hcl _ (List.mem_singleton_self _)), fun _ => ⟨m, σ, rfl, ?_,
        ?_, ?_⟩⟩
      · simpa [simPks] using hv
      · simpa [hb, hhist] using hm
      · simp only [run_ret, List.append_nil]
        intro hm'
        exact hm (hr2 m hm')
    · have hfn : findForgery i (simPks i pk ω) (stepCall P A ω bake p M)
          (advRaw (ω.withKey i (pk, sk)) A (stepCall P A ω bake p M)).1 = none := by
        refine findForgery_eq_none ?_
        rw [simPks_eq i pk ω sk]
        exact hF
      rw [hfn]
      refine ⟨fun _ => ⟨?_, ?_⟩, fun ⟨c, hc, hc'⟩ => absurd (List.mem_singleton.1 hc ▸ hc') hF⟩
      · simp only [run_ret]
        rw [corruptStep_eq P A i pk ω sk bake p M h]
      · simp only [run_ret, List.append_nil]
        intro b hb'
        refine hb_sStep P A (ω.withKey i (pk, sk)) bake p M b ?_
        have := hr2 b hb'
        simpa [hb, hhist] using this

theorem SimSpec.congr_calls {R : (GS P ω A ⊕ (Block Tx Hash (Fin np) × Sch.Sig)) ×
      List (Block Tx Hash (Fin np))} {calls calls' : List (CallInput Tx Hash np A.AdvState)}
    {Nin Nout : GS P ω A} (h : SimSpec P A i pk ω sk R calls Nin Nout)
    (hc : ∀ c, c ∈ calls ↔ c ∈ calls') : SimSpec P A i pk ω sk R calls' Nin Nout :=
  ⟨fun hcl => h.1 fun c hc' => hcl c ((hc c).1 hc'),
    fun ⟨c, hc', hf⟩ => h.2 ⟨c, (hc c).2 hc', hf⟩⟩

/-- Sequential composition of simulated computations. -/
theorem SimSpec.bind {prog1 : Prog (Sch := Sch) (GS P ω A ⊕ (Block Tx Hash (Fin np) × Sch.Sig))}
    {cont : GS P ω A → Prog (Sch := Sch) (GS P ω A ⊕ (Block Tx Hash (Fin np) × Sch.Sig))}
    {calls1 calls2 : List (CallInput Tx Hash np A.AdvState)} {N0 N1 N2 : GS P ω A}
    (h1 : SimSpec P A i pk ω sk (run (Sch.sign sk) prog1) calls1 N0 N1)
    (h2 : SimSpec P A i pk ω sk (run (Sch.sign sk) (cont N1)) calls2 N1 N2)
    (hm01 : ∀ b ∈ hb P A N0, b ∈ hb P A N1) (hm12 : ∀ b ∈ hb P A N1, b ∈ hb P A N2) :
    SimSpec P A i pk ω sk (run (Sch.sign sk) (prog1.bind fun r => match r with
      | Sum.inl M => cont M
      | Sum.inr fg => .ret (Sum.inr fg))) (calls1 ++ calls2) N0 N2 := by
  rw [run_bind]
  by_cases hf1 : ∃ c ∈ calls1, ForgedBy (ω.withKey i (pk, sk)) A i c
  · obtain ⟨m, σ, hr, hv, hn0, hnl⟩ := h1.2 hf1
    rw [hr]
    simp only [run_ret, List.append_nil]
    refine ⟨fun hcl => ?_, fun _ => ⟨m, σ, rfl, hv, hn0, hnl⟩⟩
    obtain ⟨c, hc, hc'⟩ := hf1
    exact absurd hc' (hcl c (List.mem_append_left _ hc))
  · have hf1' : ∀ c ∈ calls1, ¬ForgedBy (ω.withKey i (pk, sk)) A i c :=
      fun c hc hc' => hf1 ⟨c, hc, hc'⟩
    obtain ⟨hr, hlog⟩ := h1.1 hf1'
    rw [hr]
    refine ⟨fun hcl => ?_, fun hf => ?_⟩
    · obtain ⟨hr2, hlog2⟩ := h2.1 fun c hc => hcl c (List.mem_append_right _ hc)
      exact ⟨hr2, fun b hb' => (List.mem_append.1 hb').elim (fun h => hm12 b (hlog b h))
        (hlog2 b)⟩
    · have hf2 : ∃ c ∈ calls2, ForgedBy (ω.withKey i (pk, sk)) A i c := by
        obtain ⟨c, hc, hc'⟩ := hf
        rcases List.mem_append.1 hc with hc | hc
        · exact absurd hc' (hf1' c hc)
        · exact ⟨c, hc, hc'⟩
      obtain ⟨m, σ, hr2, hv, hn1, hnl2⟩ := h2.2 hf2
      exact ⟨m, σ, hr2, hv, fun h => hn1 (hm01 m h),
        fun h => (List.mem_append.1 h).elim (fun h => hn1 (hlog m h)) hnl2⟩

theorem hb_foldr (bake : Bool) (N : GS P ω A) (l : List (Fin np)) :
    ∀ b ∈ hb P A N, b ∈ hb P A (l.foldr (sStep P A ω bake) N) := by
  induction l with
  | nil => exact fun b h => h
  | cons p ps ih => exact fun b h => hb_sStep P A ω bake p _ b (ih b h)

theorem run_simFold (bake : Bool) (N : GS P ω A) (l : List (Fin np)) :
    SimSpec P A i pk ω sk (run (Sch.sign sk) (simFold P A i pk ω bake N l))
      ((foldrCalls (sStep P A (ω.withKey i (pk, sk)) bake) N l).flatMap
        (stepCalls P (ω.withKey i (pk, sk)) A bake)) N
      (l.foldr (sStep P A (ω.withKey i (pk, sk)) bake) N) := by
  induction l with
  | nil =>
    refine ⟨fun _ => ⟨rfl, by simp [simFold]⟩, ?_⟩
    rintro ⟨c, hc, _⟩; simp [foldrCalls] at hc
  | cons p ps ih =>
    have h := SimSpec.bind P A i pk ω sk ih
      (run_simStep P A i pk ω sk bake p (ps.foldr (sStep P A (ω.withKey i (pk, sk)) bake) N))
      (hb_foldr P A (ω.withKey i (pk, sk)) bake N ps)
      (hb_sStep P A (ω.withKey i (pk, sk)) bake p _)
    refine SimSpec.congr_calls P A i pk ω sk h fun c => ?_
    simp only [foldrCalls, List.flatMap_cons, List.mem_append]
    exact or_comm

theorem hb_sPhase (N : GS P ω A) : ∀ b ∈ hb P A N, b ∈ hb P A (sPhase P ω A false N) := by
  intro b h
  rw [sPhase_def]
  let _ := ω.params P; let _ := ω.bparams P
  cases N.progress with
  | Ready => exact hb_foldr P A ω false N N.exec_order b h
  | Delivered => exact hb_foldr P A ω true N N.exec_order b h
  | Baked => exact h

theorem run_simPhase (N : GS P ω A) :
    SimSpec P A i pk ω sk (run (Sch.sign sk) (simPhase P A i pk ω N))
      (phaseCalls P (ω.withKey i (pk, sk)) A N) N (sPhase P (ω.withKey i (pk, sk)) A false N) := by
  let _ := ω.params P; let _ := ω.bparams P
  rw [sPhase_def]
  unfold simPhase phaseCalls
  cases hp : N.progress with
  | Ready =>
    dsimp only
    have h := run_simFold P A i pk ω sk false N N.exec_order
    rw [run_bind]
    simp only [run_ret, List.append_nil]
    refine ⟨fun hcl => ?_, fun hf => ?_⟩
    · obtain ⟨hr, hlog⟩ := h.1 hcl
      rw [hr]
      exact ⟨rfl, hlog⟩
    · obtain ⟨m, σ, hr, hv, hn, hnl⟩ := h.2 hf
      rw [hr]
      exact ⟨m, σ, rfl, hv, hn, hnl⟩
  | Delivered =>
    dsimp only
    have h := run_simFold P A i pk ω sk true N N.exec_order
    rw [run_bind]
    simp only [run_ret, List.append_nil]
    refine ⟨fun hcl => ?_, fun hf => ?_⟩
    · obtain ⟨hr, hlog⟩ := h.1 hcl
      rw [hr]
      exact ⟨rfl, hlog⟩
    · obtain ⟨m, σ, hr, hv, hn, hnl⟩ := h.2 hf
      rw [hr]
      exact ⟨m, σ, rfl, hv, hn, hnl⟩
  | Baked =>
    refine ⟨fun _ => ⟨rfl, by simp [run]⟩, ?_⟩
    rintro ⟨c, hc, _⟩; simp at hc

theorem traceCalls_succ (ω : Seed Tx Hash np n Hz Sch) (k : ℕ) :
    traceCalls P ω A (k + 1) = traceCalls P ω A k ++ phaseCalls P ω A (sTrace P ω A false k) := by
  simp [traceCalls, List.range_succ, List.flatMap_append]

theorem run_simTrace (k : ℕ) :
    SimSpec P A i pk ω sk (run (Sch.sign sk) (simTrace P A i pk ω k))
      (traceCalls P (ω.withKey i (pk, sk)) A k) (sTrace P ω A false 0)
      (sTrace P (ω.withKey i (pk, sk)) A false k) := by
  induction k with
  | zero =>
    refine ⟨fun _ => ⟨rfl, by simp [simTrace]⟩, ?_⟩
    rintro ⟨c, hc, _⟩; simp [traceCalls] at hc
  | succ k ih =>
    have h := SimSpec.bind P A i pk ω sk ih (run_simPhase P A i pk ω sk _)
      (fun b hb' => by
        let _ := ω.params P; let _ := ω.bparams P
        simp [hb, sTrace, runTrace, N0] at hb')
      (hb_sPhase P A (ω.withKey i (pk, sk)) _)
    rw [traceCalls_succ, sTrace_succ]
    exact h

/-- **The forger wins on a forgery.** If the adversary forges a block of party `i` in the
first `K` phases of the real execution for the seed `ω` with the key pair `(pk, sk)` for party
`i`, the forger with verification key `pk`, signing oracle `Sch.sign sk` and coins `ω` outputs
a message with a valid signature that it did not query. -/
theorem forger_wins (K : ℕ) (h : ForgeBy P (ω.withKey i (pk, sk)) A K i) :
    ∃ m σ, (run (Sch.sign sk) (forgerProg P A i pk ω K)).1 = some (m, σ) ∧
      Sch.verify pk m σ = true ∧ m ∉ (run (Sch.sign sk) (forgerProg P A i pk ω K)).2 := by
  obtain ⟨m, σ, hr, hv, _, hnl⟩ := (run_simTrace P A i pk ω sk K).2 h
  refine ⟨m, σ, ?_, hv, ?_⟩
  · rw [forgerProg, run_bind, hr]; rfl
  · rw [forgerProg, run_bind, hr]
    simpa using hnl

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

section Prob

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] [Fintype Tx] [Fintype Hash]
  [Nonempty Hash] {np : ℕ} [Corruption (Fin np)] {n Hz : ℕ}
  {Sch : SigScheme (Block Tx Hash (Fin np))}

/-- The distribution of the key pairs: independent key generation for every party. -/
noncomputable def keyDist (Sch : SigScheme (Block Tx Hash (Fin np))) :
    PMF (Fin np → Sch.PK × Sch.SK) :=
  PMF.piFin fun _ => Sch.keygen

/-- The distribution of the random seed: the slot kinds (`kindDist ν W n`), a uniformly random
oracle, and independent key pairs, all independent. -/
noncomputable def seedDist (ν : PMF SlotKind) (W n Hz : ℕ)
    (Sch : SigScheme (Block Tx Hash (Fin np))) : PMF (Seed Tx Hash np n Hz Sch) :=
  (kindDist ν W n).bind fun κ => (uniformFun (BlockDom Tx Hash np Hz) Hash).bind fun f =>
    (keyDist Sch).bind fun ks => PMF.pure ⟨κ, f, ks⟩

theorem seedDist_withKey (ν : PMF SlotKind) (W : ℕ) (i : Fin np) :
    (seedDist ν W n Hz Sch).bind (fun ω => Sch.keygen.bind fun kp => PMF.pure (ω.withKey i kp)) =
      seedDist ν W n Hz Sch := by
  simp only [seedDist, PMF.bind_bind, PMF.pure_bind]
  congr 1; funext κ; congr 1; funext f
  conv_rhs => rw [keyDist, ← piFin_update Sch.keygen i, ← keyDist]
  simp only [PMF.bind_bind, PMF.pure_bind]

variable (P : Protocol Tx Hash np) (A : Adversary Tx Hash np n Hz Sch)

/-- **The reduction.** The EUF-CMA adversary obtained from the adversary `A` against the signed
protocol and the party `i`: its coins are a seed drawn from `seedDist`, and it runs
`forgerProg`, which simulates the first `K` phases of the real execution with the verification
key of the game for party `i` and outputs the first forgery of party `i`. -/
noncomputable def forger (ν : PMF SlotKind) (W K : ℕ) (i : Fin np) : EUFAdversary Sch where
  Coins := Seed Tx Hash np n Hz Sch
  coins := seedDist ν W n Hz Sch
  forge := fun pk ω => forgerProg P A i pk ω K

/-- **Forging a block of party `i` (part 3).** The probability that the adversary `A` forges a
block of party `i` in the first `K` phases of the real execution is at most the EUF-CMA
advantage of the explicit adversary `forger P A ν W K i`. -/
theorem prob_forgeBy_le (ν : PMF SlotKind) (W K : ℕ) (i : Fin np) :
    (seedDist ν W n Hz Sch).toOuterMeasure {ω | ForgeBy P ω A K i} ≤
      eufAdv (forger P A ν W K i) := by
  rw [eufAdv_eq]
  have hmap : (eufInputs (forger P A ν W K i)).map (fun x => x.2.withKey i x.1) =
      seedDist ν W n Hz Sch := by
    rw [← seedDist_withKey ν W i (Sch := Sch) (Hz := Hz)]
    simp only [eufInputs, forger, PMF.map_bind, PMF.pure_map]
    exact PMF.bind_comm _ _ _
  rw [← hmap, PMF.toOuterMeasure_map_apply]
  refine MeasureTheory.OuterMeasure.mono _ fun x hx => ?_
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hx ⊢
  obtain ⟨m, σ, h1, h2, h3⟩ := forger_wins P A i x.1.1 x.2 x.1.2 K hx
  simp only [eufWins, forger]
  rw [h1]
  simpa [h2] using h3

/-- **Forging an honest block.** The probability that the adversary forges an honest block in the
first `K` phases of the real execution is at most the sum over the parties `i` of the EUF-CMA
advantages of the forgers `forger P A ν W K i`. -/
theorem prob_forge_le (ν : PMF SlotKind) (W K : ℕ) :
    (seedDist ν W n Hz Sch).toOuterMeasure {ω | Forge P ω A K} ≤
      ∑ i : Fin np, eufAdv (forger P A ν W K i) := by
  have hsub : {ω | Forge P ω A K} ⊆ ⋃ i ∈ (Finset.univ : Finset (Fin np)),
      {ω | ForgeBy P ω A K i} := by
    intro ω hω
    obtain ⟨i, hi⟩ := forge_iff_exists P ω A K hω
    simp only [Set.mem_iUnion]
    exact ⟨i, Finset.mem_univ _, hi⟩
  refine (MeasureTheory.OuterMeasure.mono _ hsub).trans ?_
  refine (MeasureTheory.measure_biUnion_finset_le (μ := (seedDist ν W n Hz Sch).toOuterMeasure)
    _ _).trans ?_
  exact Finset.sum_le_sum fun i _ => prob_forgeBy_le P A ν W K i

end Prob

end CatCryptCore.Consensus.PoSNSB
