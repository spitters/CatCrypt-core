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
transactions `TxIn = Fin np × Tx`, and adversary inputs `AdvIn X`, which either run the next
phase with an index `x : X` for the corrupt calls of that phase, or query the hash function. The
execution is recomputed from the seed and the log: the honest transactions of a slot are the
latest ones recorded before the baking phase of the slot (`txOf`), and the adversary is the
adversary `F.at σ` of a family `F` along the indices `σ` of the log (`scriptOfD`); for the
indices `React` it is the script adversary `scriptAdv m σ` of the reactions of the log
(`scriptOf`).

The phases of the execution are numbered from `0`: phase `k` runs at slot `k / 3 + 1`; it is the
delivery phase when `k % 3 = 0` and the baking phase when `k % 3 = 1` (`sTrace_clock`). An
adversary call of slot `sl` belongs to phase `callIdx c = 3 (sl - 1)` (delivery) or
`3 (sl - 1) + 1` (baking).

## Main definitions

* `React` — the corrupt calls of one phase: a function of the leader string, the verification
  keys, the public inputs of the call and the signatures of the honest blocks of the history;
  it does not receive the hash function.
* `callIdx` — the phase of an adversary call.
* `AdvFamily X S`, `AdvFamily.at F σ` — a family of adversaries with state `S` indexed by `X`,
  and its adversary that answers a call of phase `i` with the action of index `σ i`;
  `AdvFamily.script m` is the family of reactions and `AdvFamily.const A` the constant family.
* `scriptAdv m σ` — the adversary with state `ℕ` (the phase of its last call) that answers a
  call of phase `i` with `σ i`, truncated to `m` messages; it ignores the hash function of the
  public information. It is `(AdvFamily.script m).at σ` (`scriptAdv_eq_at`).
* `Protocol.withTx`, `txOf` — the protocol with the transaction selection replaced, and the
  honest transactions of an input log.
* `TxIn`, `AdvIn X`, `LogEvOf X`, `LogEv`, `beforeStep`, `scriptOfD`, `scriptOf` — the inputs
  of the environment with indices `X`, the entries of the log recorded before a phase, and the
  indices of the phases of the log.

## Main results

* `ProtocolHyp.withTx` — the hypotheses on the protocol do not involve the transactions.
* `sTrace_congr_of_agree_at`, `sTrace_congr_of_agree` — the first `j` phases of the execution
  depend only on the indices of the phases before `j` and on the transactions of the slots whose
  baking phase is before `j`.
* `sTrace_script_congr_at`, `sTrace_script_congr` (causality) — the first `j` phases of the
  execution of a log depend only on the entries recorded before phase `j`.
* `sTrace_append_of_le`, `sTrace_snoc_step` — the first `j` phases of the execution of a log
  with at least `j` phase entries ignore what is appended to it, so the execution of an extended
  log is computed one phase at a time.
* `phaseCalls_congr_of_agree`, `traceCalls_congr_of_agree`, `forgedBy_congr` — the adversary
  calls of the first `j` phases, and the forgeries on them, depend only on the indices of the
  phases before `j` and on the transactions of the slots whose baking phase is before `j`.
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

/-- A family of adversaries with state `S` indexed by `X`: a start state, and for every index
`x` the action when a corrupt party bakes and when it receives messages. -/
structure AdvFamily (X S : Type) (Tx Hash : Type) (np n Hz : ℕ) (PK Sig : Type) where
  /-- The initial state. -/
  st0 : S
  /-- The action of index `x` when a corrupt party bakes. -/
  bake : X → PubInfo Tx Hash np n Hz PK → Slot → History Tx Hash (Fin np) →
    List (Block Tx Hash (Fin np) × Sig) → MessagePool Tx Hash (Fin np) → S →
      AdvOut Tx Hash np Sig × S
  /-- The action of index `x` when a corrupt party receives messages. -/
  rcv : X → PubInfo Tx Hash np n Hz PK → Messages Tx Hash (Fin np) → Slot →
    History Tx Hash (Fin np) → List (Block Tx Hash (Fin np) × Sig) →
      MessagePool Tx Hash (Fin np) → S → AdvOut Tx Hash np Sig × S

namespace AdvFamily

variable {X S : Type}

/-- The adversary of the family `F` along the indices `σ`: a call of phase `i` is answered by
the action of index `σ i`. -/
@[reducible] def «at» (F : AdvFamily X S Tx Hash np n Hz PK Sig) (σ : ℕ → X) :
    Adversary Tx Hash np n Hz PK Sig where
  AdvState := S
  st0 := F.st0
  bake pub sl hist tbl mb s :=
    F.bake (σ (callIdx (⟨none, sl, hist, mb, ()⟩ : CallInput Tx Hash np Unit))) pub sl hist tbl mb s
  rcv pub ms sl hist tbl mb s :=
    F.rcv (σ (callIdx (⟨some ms, sl, hist, mb, ()⟩ : CallInput Tx Hash np Unit))) pub ms sl hist
      tbl mb s

/-- The family of reactions: the index is a reaction, whose output is truncated to `m`
messages, and the state becomes the phase of the call. -/
@[reducible] def script (m : ℕ) : AdvFamily (React Tx Hash np n PK Sig) ℕ Tx Hash np n Hz PK Sig where
  st0 := 0
  bake r pub sl hist tbl mb _ :=
    ((r (pub.1, pub.2.2) ⟨none, sl, hist, mb, ()⟩ tbl).take m,
      callIdx (⟨none, sl, hist, mb, ()⟩ : CallInput Tx Hash np Unit))
  rcv r pub ms sl hist tbl mb _ :=
    ((r (pub.1, pub.2.2) ⟨some ms, sl, hist, mb, ()⟩ tbl).take m,
      callIdx (⟨some ms, sl, hist, mb, ()⟩ : CallInput Tx Hash np Unit))

/-- The constant family of the adversary `A`: every index acts as `A`. -/
@[reducible] def const (A : Adversary Tx Hash np n Hz PK Sig) :
    AdvFamily X A.AdvState Tx Hash np n Hz PK Sig where
  st0 := A.st0
  bake _ := A.bake
  rcv _ := A.rcv

/-- The constant family of `A` along any indices is `A`. -/
theorem const_at (A : Adversary Tx Hash np n Hz PK Sig) (σ : ℕ → X) :
    (const A : AdvFamily X A.AdvState Tx Hash np n Hz PK Sig).at σ = A := rfl

end AdvFamily

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

/-- The script adversary of `σ` is the family of reactions along `σ`. -/
theorem scriptAdv_eq_at (m : ℕ) (σ : ℕ → React Tx Hash np n PK Sig) :
    scriptAdv (Hz := Hz) m σ = (AdvFamily.script m).at σ := rfl

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

/-- Two adversaries of a family answer a call alike when their indices for its phase agree. -/
theorem advRaw_at_congr {X S : Type} (ω : Seed Tx Hash np n Hz PK SK)
    (F : AdvFamily X S Tx Hash np n Hz PK Sig) {σ σ' : ℕ → X} (c : CallInput Tx Hash np S)
    (h : σ (callIdx c) = σ' (callIdx c)) :
    advRaw Sch ω (F.at σ) c = advRaw Sch ω (F.at σ') c := by
  obtain ⟨ms, sl, hist, mb, st⟩ := c
  cases ms with
  | none =>
    have h' : σ (callIdx (⟨none, sl, hist, mb, ()⟩ : CallInput Tx Hash np Unit)) =
        σ' (callIdx (⟨none, sl, hist, mb, ()⟩ : CallInput Tx Hash np Unit)) := h
    simp only [advRaw, AdvFamily.at, h']
  | some ms =>
    have h' : σ (callIdx (⟨some ms, sl, hist, mb, ()⟩ : CallInput Tx Hash np Unit)) =
        σ' (callIdx (⟨some ms, sl, hist, mb, ()⟩ : CallInput Tx Hash np Unit)) := h
    simp only [advRaw, AdvFamily.at, h']

/-- Two script adversaries answer a call alike when their reactions for its phase agree. -/
theorem advRaw_scriptAdv_congr (ω : Seed Tx Hash np n Hz PK SK) (m : ℕ)
    {σ σ' : ℕ → React Tx Hash np n PK Sig} (c : CallInput Tx Hash np ℕ)
    (h : σ (callIdx c) = σ' (callIdx c)) :
    advRaw Sch ω (scriptAdv m σ) c = advRaw Sch ω (scriptAdv m σ') c :=
  advRaw_at_congr Sch ω (AdvFamily.script m) c h

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
    · rw [ite_eq_left h0] at hp
      rw [hp]
      refine ⟨?_, ?_⟩
      · dsimp only
        rw [foldr_t_now P ω A _ (sRcv_t_now Sch P ω A ideal), ht]; omega
      · dsimp only; rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    · by_cases h1 : k % 3 = 1
      · rw [ite_eq_right h0, ite_eq_left h1] at hp
        rw [hp]
        refine ⟨?_, ?_⟩
        · dsimp only
          rw [foldr_t_now P ω A _ (sBake_t_now Sch P ω A ideal), ht]; omega
        · dsimp only; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      · rw [ite_eq_right h0, ite_eq_right h1] at hp
        rw [hp]
        refine ⟨?_, ?_⟩
        · dsimp only
          show (sTrace Sch P ω A ideal k).t_now + 1 = _
          rw [ht]; omega
        · dsimp only; rw [ite_eq_left (by omega)]

end Clock

/-! ## Causality -/

section Causality

variable (P : Protocol Tx Hash np n Hz) (ω : Seed Tx Hash np n Hz PK SK) (m : ℕ)

variable {X S : Type} (F : AdvFamily X S Tx Hash np n Hz PK Sig)

/-- A receiving step at slot `sl` depends on the indices of a family only through the index of
phase `3 (sl - 1)`, and not on the transactions. -/
theorem sRcv_at_congr (ideal : Bool) (t t' : Slot → Fin np → Tx)
    (σ σ' : ℕ → X) (p : Fin np)
    (M : GS (P.withTx t) ω (F.at σ))
    (h : σ (3 * ((letI := ω.params P; letI := ω.bparams P; M.t_now) - 1)) =
      σ' (3 * ((letI := ω.params P; letI := ω.bparams P; M.t_now) - 1))) :
    sRcv Sch (P.withTx t) ω (F.at σ) ideal p M =
      sRcv Sch (P.withTx t') ω (F.at σ') ideal p M := by
  let _ := ω.params P; let _ := ω.bparams P
  have e : ∀ ms sl hist mb st, σ (3 * (sl - 1)) = σ' (3 * (sl - 1)) →
      (mkExec Sch ideal (P.withTx t) ω (F.at σ)).AdversarialRcv ms sl hist mb st =
        (mkExec Sch ideal (P.withTx t') ω (F.at σ')).AdversarialRcv ms sl hist mb st := by
    intro ms sl hist mb st hσ
    rw [mkExec_rcv, advRaw_at_congr Sch ω F _ (by simpa [callIdx] using hσ)]
    rfl
  unfold sRcv party_rcv_step_world
  cases hs : M.state_map p with
  | none => rfl
  | some l =>
    by_cases hc : is_corrupt p
    · simp only [hc, Bool.not_true, Bool.false_eq_true, ite_false]
      have hf : (fetch_msgs p M).2.t_now = M.t_now := by
        simp [fetch_msgs, rmv_zero_msgs]
      rw [e _ _ _ _ _ (by rw [hf]; exact h)]
    · simp only [hc]
      rfl

/-- A baking step of party `p` at slot `sl` depends on the indices of a family only through the
index of phase `3 (sl - 1) + 1`, and on the transactions only through the transaction of `p` at
`sl`. -/
theorem sBake_at_congr (ideal : Bool) (t t' : Slot → Fin np → Tx)
    (σ σ' : ℕ → X) (p : Fin np)
    (M : GS (P.withTx t) ω (F.at σ))
    (h : σ (3 * ((letI := ω.params P; letI := ω.bparams P; M.t_now) - 1) + 1) =
      σ' (3 * ((letI := ω.params P; letI := ω.bparams P; M.t_now) - 1) + 1))
    (htx : t (letI := ω.params P; letI := ω.bparams P; M.t_now) p =
      t' (letI := ω.params P; letI := ω.bparams P; M.t_now) p) :
    sBake Sch (P.withTx t) ω (F.at σ) ideal p M =
      sBake Sch (P.withTx t') ω (F.at σ') ideal p M := by
  let _ := ω.params P; let _ := ω.bparams P
  unfold sBake party_bake_step_world
  cases hs : M.state_map p with
  | none => rfl
  | some l =>
    by_cases hc : is_corrupt p
    · simp only [hc, Bool.not_true, Bool.false_eq_true, ite_false]
      have e : (mkExec Sch ideal (P.withTx t) ω (F.at σ)).AdversarialBake M.t_now
          M.history M.msg_buff M.adv_state =
          (mkExec Sch ideal (P.withTx t') ω (F.at σ')).AdversarialBake M.t_now
            M.history M.msg_buff M.adv_state := by
        rw [mkExec_bake, advRaw_at_congr Sch ω F _ (by simpa [callIdx] using h)]
        rfl
      rw [e]
    · simp only [hc]
      have e : (mkExec Sch ideal (P.withTx t) ω (F.at σ)).TxSelection M.t_now p =
          (mkExec Sch ideal (P.withTx t') ω (F.at σ')).TxSelection M.t_now p := htx
      rw [e]
      rfl

/-- **Causality for indices and transactions.** The first `j` phases of the execution of the
adversaries of a family depend only on the indices of the phases before `j` and on the
transactions of the slots whose baking phase is before `j`. -/
theorem sTrace_congr_of_agree_at (ideal : Bool) (j : ℕ) (t t' : Slot → Fin np → Tx)
    (σ σ' : ℕ → X) (hσ : ∀ i < j, σ i = σ' i)
    (ht : ∀ sl p, 3 * (sl - 1) + 1 < j → t sl p = t' sl p) :
    ∀ k ≤ j, sTrace Sch (P.withTx t) ω (F.at σ) ideal k =
      sTrace Sch (P.withTx t') ω (F.at σ') ideal k := by
  let _ := ω.params P; let _ := ω.bparams P
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    have hkj : k < j := by omega
    rw [sTrace_succ, sTrace_succ, ← ih (by omega)]
    obtain ⟨hT, hp⟩ := sTrace_clock Sch (P.withTx t) ω (F.at σ) ideal k
    set N := sTrace Sch (P.withTx t) ω (F.at σ) ideal k with hN
    rw [sPhase_def, sPhase_def]
    unfold progOf at hp
    by_cases h0 : k % 3 = 0
    · rw [ite_eq_left h0] at hp
      rw [hp]
      dsimp only
      have hf : N.exec_order.foldr (sRcv Sch (P.withTx t) ω (F.at σ) ideal) N =
          N.exec_order.foldr (sRcv Sch (P.withTx t') ω (F.at σ') ideal) N := by
        refine foldr_congr_of_inv _ _
          (fun M : GS (P.withTx t) ω (F.at σ) => M.t_now = N.t_now)
          ?_ ?_ _ _ ?_
        · intro p M hM
          exact (sRcv_t_now Sch _ ω _ ideal p M).trans hM
        · intro p M hM
          exact sRcv_at_congr Sch P ω F ideal t t' σ σ' p M
            (hσ _ (by rw [hM, hT]; omega))
        · rfl
      rw [hf]
    · by_cases h1 : k % 3 = 1
      · rw [ite_eq_right h0, ite_eq_left h1] at hp
        rw [hp]
        dsimp only
        have hf : N.exec_order.foldr (sBake Sch (P.withTx t) ω (F.at σ) ideal) N =
            N.exec_order.foldr (sBake Sch (P.withTx t') ω (F.at σ') ideal) N := by
          refine foldr_congr_of_inv _ _
            (fun M : GS (P.withTx t) ω (F.at σ) => M.t_now = N.t_now)
            ?_ ?_ _ _ ?_
          · intro p M hM
            exact (sBake_t_now Sch _ ω _ ideal p M).trans hM
          · intro p M hM
            exact sBake_at_congr Sch P ω F ideal t t' σ σ' p M
              (hσ _ (by rw [hM, hT]; omega)) (ht _ _ (by rw [hM, hT]; omega))
          · rfl
        rw [hf]
      · rw [ite_eq_right h0, ite_eq_right h1] at hp
        rw [hp]

/-- A receiving step at slot `sl` depends on the reactions only through the reaction of phase
`3 (sl - 1)`, and not on the transactions. -/
theorem sRcv_script_congr (ideal : Bool) (t t' : Slot → Fin np → Tx)
    (σ σ' : ℕ → React Tx Hash np n PK Sig) (p : Fin np)
    (M : GS (P.withTx t) ω (scriptAdv (Hz := Hz) m σ))
    (h : σ (3 * ((letI := ω.params P; letI := ω.bparams P; M.t_now) - 1)) =
      σ' (3 * ((letI := ω.params P; letI := ω.bparams P; M.t_now) - 1))) :
    sRcv Sch (P.withTx t) ω (scriptAdv m σ) ideal p M =
      sRcv Sch (P.withTx t') ω (scriptAdv m σ') ideal p M :=
  sRcv_at_congr Sch P ω (AdvFamily.script m) ideal t t' σ σ' p M h

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
      sBake Sch (P.withTx t') ω (scriptAdv m σ') ideal p M :=
  sBake_at_congr Sch P ω (AdvFamily.script m) ideal t t' σ σ' p M h htx

/-- **Causality for reactions and transactions.** The first `j` phases of the execution depend
only on the reactions of the phases before `j` and on the transactions of the slots whose baking
phase is before `j`. -/
theorem sTrace_congr_of_agree (ideal : Bool) (j : ℕ) (t t' : Slot → Fin np → Tx)
    (σ σ' : ℕ → React Tx Hash np n PK Sig) (hσ : ∀ i < j, σ i = σ' i)
    (ht : ∀ sl p, 3 * (sl - 1) + 1 < j → t sl p = t' sl p) :
    ∀ k ≤ j, sTrace Sch (P.withTx t) ω (scriptAdv (Hz := Hz) m σ) ideal k =
      sTrace Sch (P.withTx t') ω (scriptAdv m σ') ideal k :=
  sTrace_congr_of_agree_at Sch P ω (AdvFamily.script m) ideal j t t' σ σ' hσ ht

/-! ## Input logs -/

/-- An honest input: a transaction for a party. -/
abbrev TxIn (Tx : Type) (np : ℕ) := Fin np × Tx

/-- An adversary input with indices `X`: run the next phase with the index `x` for its corrupt
calls, or query the hash function at a point. -/
inductive AdvIn (X : Type) (Tx Hash : Type) (np Hz : ℕ) where
  /-- Run the next phase with the index `x`. -/
  | step (x : X)
  /-- Query the hash function at `d`. -/
  | hash (d : BlockDom Tx Hash np Hz)

/-- An entry of an input log with indices `X`. -/
abbrev LogEvOf (X : Type) (Tx Hash : Type) (np Hz : ℕ) :=
  TxIn Tx np ⊕ AdvIn X Tx Hash np Hz

/-- An entry of the input log whose indices are reactions. -/
abbrev LogEv (Tx Hash : Type) (np n Hz : ℕ) (PK Sig : Type) :=
  LogEvOf (React Tx Hash np n PK Sig) Tx Hash np Hz

/-- The index of a log entry that runs a phase. -/
def stepOf : LogEvOf X Tx Hash np Hz → Option X
  | .inr (.step r) => some r
  | _ => none

/-- The entries of a log recorded before its `k`-th phase entry (numbered from `0`); the whole
log if it has at most `k` phase entries. -/
def beforeStep : ℕ → List (LogEvOf X Tx Hash np Hz) → List (LogEvOf X Tx Hash np Hz)
  | _, [] => []
  | k, e :: l =>
    match stepOf e, k with
    | some _, 0 => []
    | some _, k + 1 => e :: beforeStep k l
    | none, k => e :: beforeStep k l

/-- The indices of the phase entries of a log, in order. -/
def steps (log : List (LogEvOf X Tx Hash np Hz)) : List X :=
  log.filterMap stepOf

/-- The indices of the phases of a log: the `i`-th phase entry, or the default `x₀`. -/
def scriptOfD (x₀ : X) (log : List (LogEvOf X Tx Hash np Hz)) (i : ℕ) : X :=
  (steps log).getD i x₀

/-- The reactions of the phases of a log: the `i`-th phase entry, or the silent reaction. -/
def scriptOf (log : List (LogEv Tx Hash np n Hz PK Sig)) (i : ℕ) : React Tx Hash np n PK Sig :=
  scriptOfD React.silent log i

/-- The transaction of a log entry for the party `p`. -/
def txFor (p : Fin np) : LogEvOf X Tx Hash np Hz → Option Tx
  | .inl q => if q.1 = p then some q.2 else none
  | .inr _ => none

/-- The honest transactions of a log: for slot `sl` and party `p`, the latest transaction for
`p` recorded before the baking phase `3 (sl - 1) + 1` of the slot, and `d sl p` if there is
none. -/
def txOf (d : Slot → Fin np → Tx) (log : List (LogEvOf X Tx Hash np Hz)) (sl : Slot)
    (p : Fin np) : Tx :=
  (((beforeStep (3 * (sl - 1) + 1) log).filterMap (txFor p)).getLast?).getD (d sl p)

/-- The indices recorded before the `j`-th phase entry are the first `j` indices. -/
theorem steps_beforeStep (j : ℕ) (log : List (LogEvOf X Tx Hash np Hz)) :
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
theorem beforeStep_beforeStep {k j : ℕ} (hkj : k ≤ j) (log : List (LogEvOf X Tx Hash np Hz)) :
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

/-- The indices of the phases before `j` depend only on the entries recorded before the
`j`-th phase entry. -/
theorem scriptOfD_congr (x₀ : X) {j : ℕ} {log log' : List (LogEvOf X Tx Hash np Hz)}
    (h : beforeStep j log = beforeStep j log') {i : ℕ} (hi : i < j) :
    scriptOfD x₀ log i = scriptOfD x₀ log' i := by
  have e : ∀ l : List (LogEvOf X Tx Hash np Hz),
      scriptOfD x₀ l i = scriptOfD x₀ (beforeStep j l) i := by
    intro l
    unfold scriptOfD
    rw [steps_beforeStep]
    simp [List.getD_eq_getElem?_getD, hi]
  rw [e log, e log', h]

/-- The reactions of the phases before `j` depend only on the entries recorded before the
`j`-th phase entry. -/
theorem scriptOf_congr {j : ℕ} {log log' : List (LogEv Tx Hash np n Hz PK Sig)}
    (h : beforeStep j log = beforeStep j log') {i : ℕ} (hi : i < j) :
    scriptOf log i = scriptOf log' i :=
  scriptOfD_congr React.silent h hi

/-- The transactions of the slots whose baking phase is before `j` depend only on the entries
recorded before the `j`-th phase entry. -/
theorem txOf_congr (d : Slot → Fin np → Tx) {j : ℕ} {log log' : List (LogEvOf X Tx Hash np Hz)}
    (h : beforeStep j log = beforeStep j log') (sl : Slot) (p : Fin np)
    (hsl : 3 * (sl - 1) + 1 < j) : txOf d log sl p = txOf d log' sl p := by
  unfold txOf
  rw [← beforeStep_beforeStep (le_of_lt hsl) log, h, beforeStep_beforeStep (le_of_lt hsl)]

/-- **Causality for a family.** The first `j` phases of the execution of an input log with the
adversaries of a family depend only on the entries recorded before the `j`-th phase entry. -/
theorem sTrace_script_congr_at (ideal : Bool) (x₀ : X) (d : Slot → Fin np → Tx) (j : ℕ)
    {log log' : List (LogEvOf X Tx Hash np Hz)} (h : beforeStep j log = beforeStep j log') :
    ∀ k ≤ j, sTrace Sch (P.withTx (txOf d log)) ω (F.at (scriptOfD x₀ log)) ideal k =
      sTrace Sch (P.withTx (txOf d log')) ω (F.at (scriptOfD x₀ log')) ideal k :=
  sTrace_congr_of_agree_at Sch P ω F ideal j _ _ _ _ (fun _ hi => scriptOfD_congr x₀ h hi)
    (fun sl p hsl => txOf_congr d h sl p hsl)

/-- **Causality.** The first `j` phases of the execution of an input log depend only on the
entries recorded before the `j`-th phase entry. -/
theorem sTrace_script_congr (ideal : Bool) (d : Slot → Fin np → Tx) (j : ℕ)
    {log log' : List (LogEv Tx Hash np n Hz PK Sig)} (h : beforeStep j log = beforeStep j log') :
    ∀ k ≤ j, sTrace Sch (P.withTx (txOf d log)) ω (scriptAdv (Hz := Hz) m (scriptOf log)) ideal k =
      sTrace Sch (P.withTx (txOf d log')) ω (scriptAdv m (scriptOf log')) ideal k :=
  sTrace_script_congr_at Sch P ω (AdvFamily.script m) ideal React.silent d j h

/-! ## Extending a log -/

/-- The phase entries of an appended log are those of the two parts. -/
theorem steps_append (log l : List (LogEvOf X Tx Hash np Hz)) :
    steps (log ++ l) = steps log ++ steps l := by
  simp [steps, List.filterMap_append]

/-- Cutting a log before a phase entry that it contains ignores what is appended to it. -/
theorem beforeStep_append {j : ℕ} {log : List (LogEvOf X Tx Hash np Hz)}
    (hj : j < (steps log).length) (l : List (LogEvOf X Tx Hash np Hz)) :
    beforeStep j (log ++ l) = beforeStep j log := by
  induction log generalizing j with
  | nil => simp [steps] at hj
  | cons e log ih =>
    cases h : stepOf e with
    | none =>
      have hj' : j < (steps log).length := by
        simpa [steps, List.filterMap_cons, h] using hj
      simp only [List.cons_append, beforeStep, h]
      rw [ih hj']
    | some r =>
      cases j with
      | zero => simp [beforeStep, h]
      | succ j =>
        have hj' : j < (steps log).length := by
          simp [steps, h] at hj
          simpa [steps] using hj
        simp only [List.cons_append, beforeStep, h]
        rw [ih hj']

/-- The index of a phase whose entry a log contains ignores what is appended to the log. -/
theorem scriptOfD_append (x₀ : X) {log : List (LogEvOf X Tx Hash np Hz)} {i : ℕ}
    (hi : i < (steps log).length) (l : List (LogEvOf X Tx Hash np Hz)) :
    scriptOfD x₀ (log ++ l) i = scriptOfD x₀ log i := by
  unfold scriptOfD
  rw [steps_append]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

/-- The transactions of a slot whose baking phase entry a log contains ignore what is appended
to the log. -/
theorem txOf_append (d : Slot → Fin np → Tx) {log : List (LogEvOf X Tx Hash np Hz)} {sl : Slot}
    (hsl : 3 * (sl - 1) + 1 < (steps log).length) (l : List (LogEvOf X Tx Hash np Hz))
    (p : Fin np) : txOf d (log ++ l) sl p = txOf d log sl p := by
  unfold txOf
  rw [beforeStep_append hsl]

/-- The first `j` phases of the execution of a log with at least `j` phase entries ignore what
is appended to the log. -/
theorem sTrace_append_of_le (ideal : Bool) (x₀ : X) (d : Slot → Fin np → Tx) {j : ℕ}
    {log : List (LogEvOf X Tx Hash np Hz)} (hj : j ≤ (steps log).length)
    (l : List (LogEvOf X Tx Hash np Hz)) :
    ∀ k ≤ j, sTrace Sch (P.withTx (txOf d (log ++ l))) ω (F.at (scriptOfD x₀ (log ++ l))) ideal k =
      sTrace Sch (P.withTx (txOf d log)) ω (F.at (scriptOfD x₀ log)) ideal k :=
  sTrace_congr_of_agree_at Sch P ω F ideal j _ _ _ _
    (fun _ hi => scriptOfD_append x₀ (by omega) l)
    (fun _ p hsl => txOf_append d (by omega) l p)

/-- **The incremental execution.** For a log with at least `j` phase entries, phase `j + 1` of
the execution of an extension of the log is one phase of the extension applied to phase `j` of
the execution of the log. -/
theorem sTrace_snoc_step (ideal : Bool) (x₀ : X) (d : Slot → Fin np → Tx) {j : ℕ}
    {log : List (LogEvOf X Tx Hash np Hz)} (hj : j ≤ (steps log).length)
    (l : List (LogEvOf X Tx Hash np Hz)) :
    sTrace Sch (P.withTx (txOf d (log ++ l))) ω (F.at (scriptOfD x₀ (log ++ l))) ideal (j + 1) =
      sPhase Sch (P.withTx (txOf d (log ++ l))) ω (F.at (scriptOfD x₀ (log ++ l))) ideal
        (sTrace Sch (P.withTx (txOf d log)) ω (F.at (scriptOfD x₀ log)) ideal j) := by
  rw [sTrace_succ, sTrace_append_of_le Sch P ω F ideal x₀ d hj l j le_rfl]

/-! ## Causality of the adversary calls -/

/-- The states of two folds whose steps agree on the states satisfying an invariant preserved
by the first steps coincide. -/
theorem foldrCalls_congr_of_inv {α β : Type*} (g g' : α → β → β) (I : β → Prop)
    (hI : ∀ a b, I b → I (g a b)) (h : ∀ a b, I b → g a b = g' a b) :
    ∀ (l : List α) (b : β), I b → foldrCalls g b l = foldrCalls g' b l := by
  intro l b hb
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [foldrCalls]
    rw [ih, foldr_congr_of_inv g g' I hI h l b hb]

/-- Two adversaries of a family forge on a call alike when their indices for its phase agree. -/
theorem forgedBy_congr {σ σ' : ℕ → X} (c : CallInput Tx Hash np S)
    (h : σ (callIdx c) = σ' (callIdx c)) :
    Forged Sch ω (F.at σ) c ↔ Forged Sch ω (F.at σ') c := by
  unfold Forged
  rw [advRaw_at_congr Sch ω F c h]

/-- **Causality of the calls of a phase.** For `k < j`, the adversary calls of phase `k` of the
execution of the adversaries of a family depend only on the indices of the phases before `j` and
on the transactions of the slots whose baking phase is before `j`. -/
theorem phaseCalls_congr_of_agree (j : ℕ) (t t' : Slot → Fin np → Tx)
    (σ σ' : ℕ → X) (hσ : ∀ i < j, σ i = σ' i)
    (ht : ∀ sl p, 3 * (sl - 1) + 1 < j → t sl p = t' sl p) {k : ℕ} (hk : k < j) :
    phaseCalls Sch (P.withTx t) ω (F.at σ) (sTrace Sch (P.withTx t) ω (F.at σ) false k) =
      phaseCalls Sch (P.withTx t') ω (F.at σ') (sTrace Sch (P.withTx t') ω (F.at σ') false k) := by
  let _ := ω.params P; let _ := ω.bparams P
  rw [← sTrace_congr_of_agree_at Sch P ω F false j t t' σ σ' hσ ht k hk.le]
  obtain ⟨hT, hp⟩ := sTrace_clock Sch (P.withTx t) ω (F.at σ) false k
  set N := sTrace Sch (P.withTx t) ω (F.at σ) false k with hN
  unfold phaseCalls
  unfold progOf at hp
  by_cases h0 : k % 3 = 0
  · rw [ite_eq_left h0] at hp
    rw [hp]
    dsimp only
    rw [foldrCalls_congr_of_inv _ _
      (fun M : GS (P.withTx t) ω (F.at σ) => M.t_now = N.t_now)
      (fun p M hM => (sRcv_t_now Sch _ ω _ false p M).trans hM)
      (fun p M hM => sRcv_at_congr Sch P ω F false t t' σ σ' p M
        (hσ _ (by rw [hM, hT]; omega))) _ _ rfl]
    rfl
  · by_cases h1 : k % 3 = 1
    · rw [ite_eq_right h0, ite_eq_left h1] at hp
      rw [hp]
      dsimp only
      rw [foldrCalls_congr_of_inv _ _
        (fun M : GS (P.withTx t) ω (F.at σ) => M.t_now = N.t_now)
        (fun p M hM => (sBake_t_now Sch _ ω _ false p M).trans hM)
        (fun p M hM => sBake_at_congr Sch P ω F false t t' σ σ' p M
          (hσ _ (by rw [hM, hT]; omega)) (ht _ _ (by rw [hM, hT]; omega))) _ _ rfl]
      rfl
    · rw [ite_eq_right h0, ite_eq_right h1] at hp
      rw [hp]

/-- **Causality of the calls.** The adversary calls of the first `j` phases of the execution of
the adversaries of a family depend only on the indices of the phases before `j` and on the
transactions of the slots whose baking phase is before `j`. -/
theorem traceCalls_congr_of_agree (j : ℕ) (t t' : Slot → Fin np → Tx)
    (σ σ' : ℕ → X) (hσ : ∀ i < j, σ i = σ' i)
    (ht : ∀ sl p, 3 * (sl - 1) + 1 < j → t sl p = t' sl p) :
    traceCalls Sch (P.withTx t) ω (F.at σ) j = traceCalls Sch (P.withTx t') ω (F.at σ') j := by
  unfold traceCalls
  refine List.flatMap_congr fun k hk => ?_
  exact phaseCalls_congr_of_agree Sch P ω F j t t' σ σ' hσ ht (List.mem_range.1 hk)

end Causality

end Script

end CatCryptCore.Consensus.PoSNSB
