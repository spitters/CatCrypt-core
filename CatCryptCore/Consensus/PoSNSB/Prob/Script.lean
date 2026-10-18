/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.PoSNSB.Prob.Erasure

/-!
# PoS-NSB: executions driven by an input log

An environment drives the execution of the signed protocol through a log of inputs: honest
transactions `TxIn = Fin np × Tx`, and adversary inputs `AdvIn`, which either run the next phase
with a reaction `React` for the corrupt calls of that phase, or query the hash function. The
execution is recomputed from the seed and the log: the honest transactions of a slot are the
latest ones recorded before the baking phase of the slot (`txOf`), and the adversary is the
script adversary `scriptAdv m σ` of the reactions of the log (`scriptOf`).

The phases of the execution are numbered from `0`: phase `k` runs at slot `k / 3 + 1`; it is the
delivery phase when `k % 3 = 0` and the baking phase when `k % 3 = 1` (`sTrace_clock`). An
adversary call of slot `sl` belongs to phase `callIdx c = 3 (sl - 1)` (delivery) or
`3 (sl - 1) + 1` (baking).

## Main definitions

* `React` — the corrupt calls of one phase: a function of the leader string, the verification
  keys, the public inputs of the call and the signatures of the honest blocks of the history;
  it does not receive the hash function.
* `callIdx` — the phase of an adversary call.
* `scriptAdv m σ` — the adversary with state `ℕ` (the phase of its last call) that answers a
  call of phase `i` with `σ i`, truncated to `m` messages; it ignores the hash function of the
  public information.
* `Protocol.withTx`, `txOf` — the protocol with the transaction selection replaced, and the
  honest transactions of an input log.
* `TxIn`, `AdvIn`, `LogEv`, `beforeStep`, `scriptOf` — the inputs of the environment, the
  entries of the log recorded before a phase, and the reactions of the log.

## Main results

* `ProtocolHyp.withTx` — the hypotheses on the protocol do not involve the transactions.
* `sTrace_congr_of_agree` — the first `j` phases of the execution depend only on the reactions
  of the phases before `j` and on the transactions of the slots whose baking phase is before
  `j`.
* `sTrace_script_congr` (causality) — the first `j` phases of the execution of a log depend
  only on the entries recorded before phase `j`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace CatCryptCore.Consensus.PoSNSB

open Parameters BlockParameters Corruption Execution
open CatCrypt.Crypto.Signatures

section Script

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ} {PK SK Sig : Type}

/-! ## Reactions and the script adversary -/

/-- The corrupt calls of one phase: from the leader string and the verification keys, the
public inputs of a call (its adversarial state is `()`) and the signatures of the honest blocks
of the history, the signed messages to send. The hash function is not an input. -/
abbrev React (Tx Hash : Type) (np n : ℕ) (PK Sig : Type) :=
  (Fin n → Option (Fin np)) × (Fin np → PK) → CallInput Tx Hash np Unit →
    List (Block Tx Hash (Fin np) × Sig) → AdvOut Tx Hash np Sig

/-- The reaction that sends no message. -/
def React.silent : React Tx Hash np n PK Sig := fun _ _ _ => []

/-- The phase of an adversary call: `3 (sl - 1)` for a receiving call of slot `sl`,
`3 (sl - 1) + 1` for a baking call. -/
def callIdx {S : Type} (c : CallInput Tx Hash np S) : ℕ :=
  3 * (c.sl - 1) + if c.msgs.isSome then 0 else 1

/-- The public inputs of a call: the call with adversarial state `()`. -/
def CallInput.pub {S : Type} (c : CallInput Tx Hash np S) : CallInput Tx Hash np Unit :=
  ⟨c.msgs, c.sl, c.hist, c.mb, ()⟩

/-- The script adversary of the reactions `σ`: a call of phase `i` is answered by `σ i`, with
the output truncated to `m` messages, and the state becomes `i`. The hash function of the public
information is not used. -/
@[reducible] def scriptAdv (m : ℕ) (σ : ℕ → React Tx Hash np n PK Sig) : Adversary Tx Hash np n Hz PK Sig where
  AdvState := ℕ
  st0 := 0
  bake pub sl hist tbl mb _ :=
    (((σ (callIdx (⟨none, sl, hist, mb, ()⟩ : CallInput Tx Hash np Unit))) (pub.1, pub.2.2)
      ⟨none, sl, hist, mb, ()⟩ tbl).take m,
      callIdx (⟨none, sl, hist, mb, ()⟩ : CallInput Tx Hash np Unit))
  rcv pub ms sl hist tbl mb _ :=
    (((σ (callIdx (⟨some ms, sl, hist, mb, ()⟩ : CallInput Tx Hash np Unit))) (pub.1, pub.2.2)
      ⟨some ms, sl, hist, mb, ()⟩ tbl).take m,
      callIdx (⟨some ms, sl, hist, mb, ()⟩ : CallInput Tx Hash np Unit))

/-- The script adversary outputs at most `m` messages per call. -/
theorem scriptAdv_outputBound (m : ℕ) (σ : ℕ → React Tx Hash np n PK Sig) :
    (scriptAdv (Hz := Hz) m σ).OutputBound m :=
  ⟨fun _ _ _ _ _ _ => List.length_take_le _ _, fun _ _ _ _ _ _ _ => List.length_take_le _ _⟩

variable (Sch : PSigScheme (Block Tx Hash (Fin np)) PK SK Sig) [hS : Sch.Deterministic]

/-- A call of the script adversary is answered by the reaction of its phase. -/
theorem advRaw_scriptAdv (ω : Seed Tx Hash np n Hz PK SK) (m : ℕ)
    (σ : ℕ → React Tx Hash np n PK Sig) (c : CallInput Tx Hash np ℕ) :
    advRaw Sch ω (scriptAdv m σ) c =
      ((σ (callIdx c) (ω.L, fun j => (ω.ks j).1) c.pub (sigTable Sch ω.ks c.hist)).take m,
        callIdx c) := by
  obtain ⟨ms, sl, hist, mb, st⟩ := c
  cases ms <;> rfl

/-- Two script adversaries answer a call alike when their reactions for its phase agree. -/
theorem advRaw_scriptAdv_congr (ω : Seed Tx Hash np n Hz PK SK) (m : ℕ)
    {σ σ' : ℕ → React Tx Hash np n PK Sig} (c : CallInput Tx Hash np ℕ)
    (h : σ (callIdx c) = σ' (callIdx c)) :
    advRaw Sch ω (scriptAdv m σ) c = advRaw Sch ω (scriptAdv m σ') c := by
  rw [advRaw_scriptAdv, advRaw_scriptAdv, h]

/-! ## Transactions -/

/-- The protocol `P` with the transaction selection `t`. -/
@[reducible] def Protocol.withTx (P : Protocol Tx Hash np n Hz) (t : Slot → Fin np → Tx) :
    Protocol Tx Hash np n Hz :=
  { P with txSel := t }

/-- The hypotheses on the protocol do not involve the transaction selection. -/
theorem ProtocolHyp.withTx {P : Protocol Tx Hash np n Hz} (h : ProtocolHyp P)
    (t : Slot → Fin np → Tx) : ProtocolHyp (P.withTx t) :=
  ⟨h.nodup, h.leader, h.longest, h.genesis_honest, h.genesis_slot⟩

/-! ## The clock of the execution -/

/-- The progress of phase `k`. -/
def progOf (k : ℕ) : Progress :=
  if k % 3 = 0 then .Ready else if k % 3 = 1 then .Delivered else .Baked

/-- A fold of steps that preserve an invariant and agree with other steps on states satisfying
it equals the fold of the other steps. -/
theorem foldr_congr_of_inv {α β : Type*} (g g' : α → β → β) (I : β → Prop)
    (hI : ∀ a b, I b → I (g a b)) (h : ∀ a b, I b → g a b = g' a b) :
    ∀ (l : List α) (b : β), I b → l.foldr g b = l.foldr g' b := by
  intro l b hb
  induction l with
  | nil => rfl
  | cons a l ih =>
    have hl : I (l.foldr g b) := by
      clear ih
      induction l with
      | nil => exact hb
      | cons a' l' ih' => exact hI _ _ ih'
    rw [List.foldr_cons, List.foldr_cons, ← ih, h _ _ hl]

section Clock

variable (P : Protocol Tx Hash np n Hz) (ω : Seed Tx Hash np n Hz PK SK)
  (A : Adversary Tx Hash np n Hz PK Sig)

/-- A receiving step keeps the slot. -/
theorem sRcv_t_now (ideal : Bool) (p : Fin np) (M : GS P ω A) :
    letI := ω.params P; letI := ω.bparams P
    (sRcv Sch P ω A ideal p M).t_now = M.t_now := by
  let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec Sch ideal P ω A
  exact rcv_t_now (N := M) p

/-- A baking step keeps the slot. -/
theorem sBake_t_now (ideal : Bool) (p : Fin np) (M : GS P ω A) :
    letI := ω.params P; letI := ω.bparams P
    (sBake Sch P ω A ideal p M).t_now = M.t_now := by
  let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec Sch ideal P ω A
  exact bake_t_now (N := M) p

/-- A fold of steps that keep the slot keeps the slot. -/
theorem foldr_t_now (g : Fin np → GS P ω A → GS P ω A)
    (hg : ∀ p M, (letI := ω.params P; letI := ω.bparams P; (g p M).t_now = M.t_now))
    (l : List (Fin np)) (N : GS P ω A) :
    letI := ω.params P; letI := ω.bparams P
    (l.foldr g N).t_now = N.t_now := by
  induction l with
  | nil => rfl
  | cons p l ih => rw [List.foldr_cons, hg, ih]

/-- **The clock.** Phase `k` of the execution runs at slot `k / 3 + 1` with progress
`progOf k`. -/
theorem sTrace_clock (ideal : Bool) (k : ℕ) :
    letI := ω.params P; letI := ω.bparams P
    (sTrace Sch P ω A ideal k).t_now = k / 3 + 1 ∧
      (sTrace Sch P ω A ideal k).progress = progOf k := by
  let _ := ω.params P; let _ := ω.bparams P
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    obtain ⟨ht, hp⟩ := ih
    rw [sTrace_succ, sPhase_def]
    unfold progOf at hp ⊢
    by_cases h0 : k % 3 = 0
    · rw [if_pos h0] at hp
      rw [hp]
      refine ⟨?_, ?_⟩
      · dsimp only
        rw [foldr_t_now P ω A _ (sRcv_t_now Sch P ω A ideal), ht]; omega
      · dsimp only; rw [if_neg (by omega), if_pos (by omega)]
    · by_cases h1 : k % 3 = 1
      · rw [if_neg h0, if_pos h1] at hp
        rw [hp]
        refine ⟨?_, ?_⟩
        · dsimp only
          rw [foldr_t_now P ω A _ (sBake_t_now Sch P ω A ideal), ht]; omega
        · dsimp only; rw [if_neg (by omega), if_neg (by omega)]
      · rw [if_neg h0, if_neg h1] at hp
        rw [hp]
        refine ⟨?_, ?_⟩
        · dsimp only
          show (sTrace Sch P ω A ideal k).t_now + 1 = _
          rw [ht]; omega
        · dsimp only; rw [if_pos (by omega)]

end Clock

/-! ## Causality -/

section Causality

variable (P : Protocol Tx Hash np n Hz) (ω : Seed Tx Hash np n Hz PK SK) (m : ℕ)

/-- A receiving step at slot `sl` depends on the reactions only through the reaction of phase
`3 (sl - 1)`, and not on the transactions. -/
theorem sRcv_script_congr (ideal : Bool) (t t' : Slot → Fin np → Tx)
    (σ σ' : ℕ → React Tx Hash np n PK Sig) (p : Fin np)
    (M : GS (P.withTx t) ω (scriptAdv (Hz := Hz) m σ))
    (h : σ (3 * ((letI := ω.params P; letI := ω.bparams P; M.t_now) - 1)) =
      σ' (3 * ((letI := ω.params P; letI := ω.bparams P; M.t_now) - 1))) :
    sRcv Sch (P.withTx t) ω (scriptAdv m σ) ideal p M =
      sRcv Sch (P.withTx t') ω (scriptAdv m σ') ideal p M := by
  let _ := ω.params P; let _ := ω.bparams P
  have e : ∀ ms sl hist mb st, σ (3 * (sl - 1)) = σ' (3 * (sl - 1)) →
      (mkExec Sch ideal (P.withTx t) ω (scriptAdv m σ)).AdversarialRcv ms sl hist mb st =
        (mkExec Sch ideal (P.withTx t') ω (scriptAdv m σ')).AdversarialRcv ms sl hist mb st := by
    intro ms sl hist mb st hσ
    rw [mkExec_rcv, advRaw_scriptAdv_congr Sch ω m _ (by simpa [callIdx] using hσ)]
    rfl
  unfold sRcv party_rcv_step_world
  cases hs : M.state_map p with
  | none => rfl
  | some l =>
    by_cases hc : is_corrupt p
    · simp only [hc, Bool.not_true, Bool.false_eq_true, if_false]
      have hf : (fetch_msgs p M).2.t_now = M.t_now := by
        simp [fetch_msgs, rmv_zero_msgs]
      rw [e _ _ _ _ _ (by rw [hf]; exact h)]
    · simp only [hc]
      rfl

/-- A baking step of party `p` at slot `sl` depends on the reactions only through the reaction
of phase `3 (sl - 1) + 1`, and on the transactions only through the transaction of `p` at
`sl`. -/
theorem sBake_script_congr (ideal : Bool) (t t' : Slot → Fin np → Tx)
    (σ σ' : ℕ → React Tx Hash np n PK Sig) (p : Fin np)
    (M : GS (P.withTx t) ω (scriptAdv (Hz := Hz) m σ))
    (h : σ (3 * ((letI := ω.params P; letI := ω.bparams P; M.t_now) - 1) + 1) =
      σ' (3 * ((letI := ω.params P; letI := ω.bparams P; M.t_now) - 1) + 1))
    (htx : t (letI := ω.params P; letI := ω.bparams P; M.t_now) p =
      t' (letI := ω.params P; letI := ω.bparams P; M.t_now) p) :
    sBake Sch (P.withTx t) ω (scriptAdv m σ) ideal p M =
      sBake Sch (P.withTx t') ω (scriptAdv m σ') ideal p M := by
  let _ := ω.params P; let _ := ω.bparams P
  unfold sBake party_bake_step_world
  cases hs : M.state_map p with
  | none => rfl
  | some l =>
    by_cases hc : is_corrupt p
    · simp only [hc, Bool.not_true, Bool.false_eq_true, if_false]
      have e : (mkExec Sch ideal (P.withTx t) ω (scriptAdv m σ)).AdversarialBake M.t_now
          M.history M.msg_buff M.adv_state =
          (mkExec Sch ideal (P.withTx t') ω (scriptAdv m σ')).AdversarialBake M.t_now
            M.history M.msg_buff M.adv_state := by
        rw [mkExec_bake, advRaw_scriptAdv_congr Sch ω m _ (by simpa [callIdx] using h)]
        rfl
      rw [e]
    · simp only [hc]
      have e : (mkExec Sch ideal (P.withTx t) ω (scriptAdv m σ)).TxSelection M.t_now p =
          (mkExec Sch ideal (P.withTx t') ω (scriptAdv m σ')).TxSelection M.t_now p := htx
      rw [e]
      rfl

/-- **Causality for reactions and transactions.** The first `j` phases of the execution depend
only on the reactions of the phases before `j` and on the transactions of the slots whose baking
phase is before `j`. -/
theorem sTrace_congr_of_agree (ideal : Bool) (j : ℕ) (t t' : Slot → Fin np → Tx)
    (σ σ' : ℕ → React Tx Hash np n PK Sig) (hσ : ∀ i < j, σ i = σ' i)
    (ht : ∀ sl p, 3 * (sl - 1) + 1 < j → t sl p = t' sl p) :
    ∀ k ≤ j, sTrace Sch (P.withTx t) ω (scriptAdv (Hz := Hz) m σ) ideal k =
      sTrace Sch (P.withTx t') ω (scriptAdv m σ') ideal k := by
  let _ := ω.params P; let _ := ω.bparams P
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    have hkj : k < j := by omega
    rw [sTrace_succ, sTrace_succ, ← ih (by omega)]
    obtain ⟨hT, hp⟩ := sTrace_clock Sch (P.withTx t) ω (scriptAdv (Hz := Hz) m σ) ideal k
    set N := sTrace Sch (P.withTx t) ω (scriptAdv (Hz := Hz) m σ) ideal k with hN
    rw [sPhase_def, sPhase_def]
    unfold progOf at hp
    by_cases h0 : k % 3 = 0
    · rw [if_pos h0] at hp
      rw [hp]
      dsimp only
      have hf : N.exec_order.foldr (sRcv Sch (P.withTx t) ω (scriptAdv m σ) ideal) N =
          N.exec_order.foldr (sRcv Sch (P.withTx t') ω (scriptAdv m σ') ideal) N := by
        refine foldr_congr_of_inv _ _
          (fun M : GS (P.withTx t) ω (scriptAdv (Hz := Hz) m σ) => M.t_now = N.t_now)
          ?_ ?_ _ _ ?_
        · intro p M hM
          exact (sRcv_t_now Sch _ ω _ ideal p M).trans hM
        · intro p M hM
          exact sRcv_script_congr Sch P ω m ideal t t' σ σ' p M
            (hσ _ (by rw [hM, hT]; omega))
        · rfl
      rw [hf]
    · by_cases h1 : k % 3 = 1
      · rw [if_neg h0, if_pos h1] at hp
        rw [hp]
        dsimp only
        have hf : N.exec_order.foldr (sBake Sch (P.withTx t) ω (scriptAdv m σ) ideal) N =
            N.exec_order.foldr (sBake Sch (P.withTx t') ω (scriptAdv m σ') ideal) N := by
          refine foldr_congr_of_inv _ _
            (fun M : GS (P.withTx t) ω (scriptAdv (Hz := Hz) m σ) => M.t_now = N.t_now)
            ?_ ?_ _ _ ?_
          · intro p M hM
            exact (sBake_t_now Sch _ ω _ ideal p M).trans hM
          · intro p M hM
            exact sBake_script_congr Sch P ω m ideal t t' σ σ' p M
              (hσ _ (by rw [hM, hT]; omega)) (ht _ _ (by rw [hM, hT]; omega))
          · rfl
        rw [hf]
      · rw [if_neg h0, if_neg h1] at hp
        rw [hp]

/-! ## Input logs -/

/-- An honest input: a transaction for a party. -/
abbrev TxIn (Tx : Type) (np : ℕ) := Fin np × Tx

/-- An adversary input: run the next phase with a reaction for its corrupt calls, or query the
hash function at a point. -/
inductive AdvIn (Tx Hash : Type) (np n Hz : ℕ) (PK Sig : Type) where
  /-- Run the next phase with the reaction `r`. -/
  | step (r : React Tx Hash np n PK Sig)
  /-- Query the hash function at `d`. -/
  | hash (d : BlockDom Tx Hash np Hz)

/-- An entry of the input log. -/
abbrev LogEv (Tx Hash : Type) (np n Hz : ℕ) (PK Sig : Type) :=
  TxIn Tx np ⊕ AdvIn Tx Hash np n Hz PK Sig

/-- The reaction of a log entry that runs a phase. -/
def stepOf : LogEv Tx Hash np n Hz PK Sig → Option (React Tx Hash np n PK Sig)
  | .inr (.step r) => some r
  | _ => none

/-- The entries of a log recorded before its `k`-th phase entry (numbered from `0`); the whole
log if it has at most `k` phase entries. -/
def beforeStep : ℕ → List (LogEv Tx Hash np n Hz PK Sig) → List (LogEv Tx Hash np n Hz PK Sig)
  | _, [] => []
  | k, e :: l =>
    match stepOf e, k with
    | some _, 0 => []
    | some _, k + 1 => e :: beforeStep k l
    | none, k => e :: beforeStep k l

/-- The reactions of a log, in order. -/
def steps (log : List (LogEv Tx Hash np n Hz PK Sig)) : List (React Tx Hash np n PK Sig) :=
  log.filterMap stepOf

/-- The reactions of the phases of a log: the `i`-th phase entry, or the silent reaction. -/
def scriptOf (log : List (LogEv Tx Hash np n Hz PK Sig)) (i : ℕ) : React Tx Hash np n PK Sig :=
  (steps log).getD i React.silent

/-- The transaction of a log entry for the party `p`. -/
def txFor (p : Fin np) : LogEv Tx Hash np n Hz PK Sig → Option Tx
  | .inl q => if q.1 = p then some q.2 else none
  | .inr _ => none

/-- The honest transactions of a log: for slot `sl` and party `p`, the latest transaction for
`p` recorded before the baking phase `3 (sl - 1) + 1` of the slot, and `d sl p` if there is
none. -/
def txOf (d : Slot → Fin np → Tx) (log : List (LogEv Tx Hash np n Hz PK Sig)) (sl : Slot)
    (p : Fin np) : Tx :=
  (((beforeStep (3 * (sl - 1) + 1) log).filterMap (txFor p)).getLast?).getD (d sl p)

/-- The reactions recorded before the `j`-th phase entry are the first `j` reactions. -/
theorem steps_beforeStep (j : ℕ) (log : List (LogEv Tx Hash np n Hz PK Sig)) :
    steps (beforeStep j log) = (steps log).take j := by
  induction log generalizing j with
  | nil => simp [beforeStep, steps]
  | cons e l ih =>
    cases h : stepOf e with
    | none =>
      simp only [beforeStep, h, steps, List.filterMap_cons] at ih ⊢
      exact ih j
    | some r =>
      cases j with
      | zero => simp [beforeStep, h, steps]
      | succ j =>
        simp only [beforeStep, h, steps, List.filterMap_cons, List.take_succ_cons] at ih ⊢
        rw [ih j]

/-- Cutting a log before the `j`-th phase entry and then before the `k`-th, for `k ≤ j`, cuts
it before the `k`-th. -/
theorem beforeStep_beforeStep {k j : ℕ} (hkj : k ≤ j) (log : List (LogEv Tx Hash np n Hz PK Sig)) :
    beforeStep k (beforeStep j log) = beforeStep k log := by
  induction log generalizing j k with
  | nil => simp [beforeStep]
  | cons e l ih =>
    cases h : stepOf e with
    | none => simp only [beforeStep, h]; rw [ih hkj]
    | some r =>
      cases j with
      | zero =>
        obtain rfl : k = 0 := by omega
        simp [beforeStep, h]
      | succ j =>
        cases k with
        | zero => simp [beforeStep, h]
        | succ k => simp only [beforeStep, h]; rw [ih (by omega)]

/-- The reactions of the phases before `j` depend only on the entries recorded before the
`j`-th phase entry. -/
theorem scriptOf_congr {j : ℕ} {log log' : List (LogEv Tx Hash np n Hz PK Sig)}
    (h : beforeStep j log = beforeStep j log') {i : ℕ} (hi : i < j) :
    scriptOf log i = scriptOf log' i := by
  have e : ∀ l : List (LogEv Tx Hash np n Hz PK Sig), scriptOf l i = scriptOf (beforeStep j l) i := by
    intro l
    unfold scriptOf
    rw [steps_beforeStep]
    simp [List.getD_eq_getElem?_getD, hi]
  rw [e log, e log', h]

/-- The transactions of the slots whose baking phase is before `j` depend only on the entries
recorded before the `j`-th phase entry. -/
theorem txOf_congr (d : Slot → Fin np → Tx) {j : ℕ} {log log' : List (LogEv Tx Hash np n Hz PK Sig)}
    (h : beforeStep j log = beforeStep j log') (sl : Slot) (p : Fin np)
    (hsl : 3 * (sl - 1) + 1 < j) : txOf d log sl p = txOf d log' sl p := by
  unfold txOf
  rw [← beforeStep_beforeStep (le_of_lt hsl) log, h, beforeStep_beforeStep (le_of_lt hsl)]

/-- **Causality.** The first `j` phases of the execution of an input log depend only on the
entries recorded before the `j`-th phase entry. -/
theorem sTrace_script_congr (ideal : Bool) (d : Slot → Fin np → Tx) (j : ℕ)
    {log log' : List (LogEv Tx Hash np n Hz PK Sig)} (h : beforeStep j log = beforeStep j log') :
    ∀ k ≤ j, sTrace Sch (P.withTx (txOf d log)) ω (scriptAdv (Hz := Hz) m (scriptOf log)) ideal k =
      sTrace Sch (P.withTx (txOf d log')) ω (scriptAdv m (scriptOf log')) ideal k :=
  sTrace_congr_of_agree Sch P ω m ideal j _ _ _ _ (fun _ hi => scriptOf_congr h hi)
    (fun sl p hsl => txOf_congr d h sl p hsl)

end Causality

end Script

end CatCryptCore.Consensus.PoSNSB
