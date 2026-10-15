/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.PoSNSB.Prob.Hash

/-!
# PoS-NSB with signed blocks: real and ideal executions

The PoS-NSB model leaves the adversary functions `AdversarialBake` and `AdversarialRcv`
unconstrained, and the theorems of the port assume `forging_free`: the adversary sends no honest
block that was not broadcast before. This file builds the executions from a signature scheme,
a random lottery, a random oracle and an adversary, so that forging freedom becomes an event
whose probability is bounded in `CatCryptCore/Consensus/PoSNSB/Prob/Reduction.lean`.

## The signed protocol

* A signature scheme `SigScheme Msg` has key generation `keygen : PMF (PK × SK)`, deterministic
  signing and verification. Its messages are the blocks.
* The random seed (`Seed`) consists of the string of slot kinds `κ` (the lottery), the random
  oracle `f : BlockDom → Hash` (the hash of a block `b` is `f (encB b)`) and a key pair for every
  party.
* An adversary (`Adversary`) is a pair of functions in the style of `AdversarialBake` and
  `AdversarialRcv` that additionally receive the public information (the lottery string, the
  random oracle and the verification keys) and the signatures of the honest blocks of the
  history (`sigTable`), and that output signed messages.
* The network accepts an adversarial message when its block has a slot at most the current
  slot and is baked by a corrupt party or carries a valid signature of its baker (`sigOK`). This
  is the real execution `mkExec false`. The ideal execution `mkExec true` also drops honest
  blocks that are not in the history (`histOK`); it is forging free by construction
  (`forging_free_ideal`).
* The execution runs the phases of `SingleStep` in order (`phaseStep`), with the scheduling of
  the parties and of the message buffer left unchanged (`runTrace`).

## Main results

* `reach_runTrace`, `runTrace_reach`: the states of the trace are reachable, and later states are
  reachable from earlier ones.
* `forging_free_ideal`: every state of the ideal execution is forging free.
* `runTrace_ideal_eq` (identical until forgery): if no adversary call of the real execution
  outputs an accepted honest block outside the history (`Forged`), the real and the ideal
  traces coincide.
* `slots_le_t_now`: every broadcast block of the real execution has a slot at most the current
  slot, so the block encoding `encB` is injective on the blocks of the trace.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace CatCryptCore.Consensus.PoSNSB

universe u v

open Parameters BlockParameters Corruption Execution

/-! ## Executions following the phases -/

section Generic

variable {Tx Hash Party AdvState : Type} [Parameters Party] [BlockParameters Tx Hash Party]
  [Execution Tx Hash Party AdvState] [Corruption Party] [DecidableEq Party]

/-- One phase of an execution: delivery, baking or the next round, as fixed by the progress of
the state. -/
def phaseStep (N : GlobalState Tx Hash Party AdvState) : GlobalState Tx Hash Party AdvState :=
  match N.progress with
  | .Ready => { N.exec_order.foldr party_rcv_step_world N with progress := .Delivered }
  | .Delivered => { N.exec_order.foldr party_bake_step_world N with progress := .Baked }
  | .Baked => { inc_round (round_tick N) with progress := .Ready }

theorem step_phaseStep (N : GlobalState Tx Hash Party AdvState) : N ⤳ phaseStep N := by
  unfold phaseStep
  cases h : N.progress
  · exact SingleStep.Deliver N h
  · exact SingleStep.Bake N h
  · exact SingleStep.NextRound N h

variable (AdvState) in
/-- The state after `k` phases from the initial state. -/
def runTrace (k : ℕ) : GlobalState Tx Hash Party AdvState := phaseStep^[k] (N0 AdvState)

theorem runTrace_succ (k : ℕ) :
    runTrace AdvState (k + 1) = phaseStep (runTrace (Tx := Tx) (Hash := Hash) (Party := Party)
      AdvState k) :=
  Function.iterate_succ_apply' _ _ _

/-- Later states of the trace are reachable from earlier ones. -/
theorem runTrace_reach {j k : ℕ} (h : j ≤ k) :
    runTrace (Tx := Tx) (Hash := Hash) (Party := Party) AdvState j ⇓ runTrace AdvState k := by
  induction k, h using Nat.le_induction with
  | base => exact Relation.ReflTransGen.refl
  | succ k _ ih => rw [runTrace_succ]; exact ih.tail (step_phaseStep _)

/-- The states of the trace are reachable. -/
theorem reach_runTrace (k : ℕ) :
    N0 AdvState ⇓ runTrace (Tx := Tx) (Hash := Hash) (Party := Party) AdvState k :=
  runTrace_reach (j := 0) (Nat.zero_le k)

theorem phaseStep_t_now (N : GlobalState Tx Hash Party AdvState) :
    (phaseStep N).t_now ≤ N.t_now + 1 := by
  unfold phaseStep
  cases N.progress
  · simp only; rw [show ∀ ps : List Party, (ps.foldr party_rcv_step_world N).t_now = N.t_now from
      fun ps => by induction ps with
        | nil => rfl
        | cons p ps ih => rw [List.foldr_cons, rcv_t_now, ih]]
    omega
  · simp only; rw [show ∀ ps : List Party, (ps.foldr party_bake_step_world N).t_now = N.t_now from
      fun ps => by induction ps with
        | nil => rfl
        | cons p ps ih => rw [List.foldr_cons, bake_t_now, ih]]
    omega
  · simp [inc_round, round_tick]

/-- After `k` phases the slot is at most `k + 1`. -/
theorem runTrace_t_now (k : ℕ) :
    (runTrace (Tx := Tx) (Hash := Hash) (Party := Party) AdvState k).t_now ≤ k + 1 := by
  induction k with
  | zero => simp [runTrace, N0]
  | succ k ih =>
    rw [runTrace_succ]
    have := phaseStep_t_now (runTrace (Tx := Tx) (Hash := Hash) (Party := Party) AdvState k)
    omega

end Generic

/-- The states at which the steps of `ps.foldr g N` are applied, with the party of each step. -/
def foldrCalls {α : Type u} {β : Type v} (g : α → β → β) (N : β) : List α → List (α × β)
  | [] => []
  | p :: ps => (p, ps.foldr g N) :: foldrCalls g N ps

/-- Two folds coincide if the steps coincide at every state at which the first fold applies a
step. -/
theorem foldr_congr_calls {α : Type u} {β : Type v} (g g' : α → β → β) (N : β) (l : List α)
    (h : ∀ c ∈ foldrCalls g N l, g' c.1 c.2 = g c.1 c.2) : l.foldr g' N = l.foldr g N := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    rw [List.foldr_cons, List.foldr_cons, ih fun c hc => h c (List.mem_cons_of_mem _ hc)]
    exact h (p, ps.foldr g N) (by simp [foldrCalls])

/-! ## Signature schemes -/

/-- A signature scheme with deterministic signing on messages of type `Msg`. -/
structure SigScheme (Msg : Type) where
  /-- Verification keys. -/
  PK : Type
  /-- Signing keys. -/
  SK : Type
  /-- Signatures. -/
  Sig : Type
  /-- Key generation. -/
  keygen : PMF (PK × SK)
  /-- Signing. -/
  sign : SK → Msg → Sig
  /-- Verification. -/
  verify : PK → Msg → Sig → Bool

/-! ## The signed protocol -/

deriving instance DecidableEq for Block
deriving instance DecidableEq for Message

/-- The domain of the random oracle: blocks with slots reduced modulo `Hz + 1`. -/
abbrev BlockDom (Tx Hash : Type) (np Hz : ℕ) := Fin (Hz + 1) × Tx × Hash × Fin np

section Signed

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]

/-- The encoding of a block into the domain of the random oracle. -/
def encB (Hz : ℕ) (b : Block Tx Hash (Fin np)) : BlockDom Tx Hash np Hz :=
  (⟨b.sl % (Hz + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩, b.txs, b.pred, b.bid)

/-- The encoding is injective on blocks with slot at most `Hz`. -/
theorem encB_inj {Hz : ℕ} {b b' : Block Tx Hash (Fin np)} (h : b.sl ≤ Hz) (h' : b'.sl ≤ Hz)
    (he : encB Hz b = encB Hz b') : b = b' := by
  obtain ⟨s, t, p, i⟩ := b
  obtain ⟨s', t', p', i'⟩ := b'
  simp only [encB, Prod.mk.injEq, Fin.mk.injEq] at he
  obtain ⟨h1, rfl, rfl, rfl⟩ := he
  rw [Nat.mod_eq_of_lt (by simp at h; omega), Nat.mod_eq_of_lt (by simp at h'; omega)] at h1
  rw [h1]

variable {n Hz : ℕ}

/-- The fixed parameters of the protocol: the initial parties, the lottery map, the genesis
block, the tree type of each party for every string of slot kinds and every random oracle, and
the selection of transactions. -/
structure Protocol (Tx Hash : Type) (np n Hz : ℕ) where
  /-- The initial parties. -/
  IP : List (Fin np)
  /-- The lottery map from slot kinds to leaders. -/
  lot : SlotKind → Fin np → Bool
  /-- The genesis block. -/
  GB : Block Tx Hash (Fin np)
  /-- The tree type of each party. -/
  trees : (κ : Fin n → SlotKind) → (f : BlockDom Tx Hash np Hz → Hash) → Fin np →
    @TreeType Tx Hash (Fin np) (lotteryParams IP lot κ) ⟨GB, fun b => f (encB Hz b)⟩
  /-- The transactions of honest blocks. -/
  txSel : Slot → Fin np → Tx

/-- The random seed of an execution: the slot kinds of the first `n` slots, the random oracle,
and a key pair for every party. -/
structure Seed (Tx Hash : Type) (np n Hz : ℕ) (Sch : SigScheme (Block Tx Hash (Fin np))) where
  /-- The slot kinds. -/
  κ : Fin n → SlotKind
  /-- The random oracle. -/
  f : BlockDom Tx Hash np Hz → Hash
  /-- The key pairs. -/
  ks : Fin np → Sch.PK × Sch.SK

variable {Sch : SigScheme (Block Tx Hash (Fin np))}

/-- The lottery of a seed. -/
abbrev Seed.params (P : Protocol Tx Hash np n Hz) (ω : Seed Tx Hash np n Hz Sch) :
    Parameters (Fin np) :=
  lotteryParams P.IP P.lot ω.κ

/-- The genesis block and the hash function `b ↦ f (encB b)` of a seed. -/
abbrev Seed.bparams (P : Protocol Tx Hash np n Hz) (ω : Seed Tx Hash np n Hz Sch) :
    BlockParameters Tx Hash (Fin np) :=
  ⟨P.GB, fun b => ω.f (encB Hz b)⟩

/-- The public information of a seed: the lottery string, the random oracle and the
verification keys. -/
abbrev PubInfo (Tx Hash : Type) (np n Hz : ℕ) (Sch : SigScheme (Block Tx Hash (Fin np))) :=
  (Fin n → SlotKind) × (BlockDom Tx Hash np Hz → Hash) × (Fin np → Sch.PK)

/-- The public information of a seed. -/
def Seed.pub (ω : Seed Tx Hash np n Hz Sch) : PubInfo Tx Hash np n Hz Sch :=
  (ω.κ, ω.f, fun j => (ω.ks j).1)

/-- The output of the adversary: signed messages with their delays. -/
abbrev AdvOut (Tx Hash : Type) (np : ℕ) (Sig : Type) :=
  List ((Message Tx Hash (Fin np) × Sig) × DelayMap (Fin np))

/-- An adversary against the signed protocol. Besides the inputs of the PoS-NSB adversary
functions, it receives the public information and the signatures of the honest blocks of the
history, and it outputs signed messages. -/
structure Adversary (Tx Hash : Type) (np n Hz : ℕ) (Sch : SigScheme (Block Tx Hash (Fin np))) where
  /-- The state of the adversary. -/
  AdvState : Type
  /-- The initial state. -/
  st0 : AdvState
  /-- The action when a corrupt party bakes. -/
  bake : PubInfo Tx Hash np n Hz Sch → Slot → History Tx Hash (Fin np) →
    List (Block Tx Hash (Fin np) × Sch.Sig) → MessagePool Tx Hash (Fin np) → AdvState →
      AdvOut Tx Hash np Sch.Sig × AdvState
  /-- The action when a corrupt party receives messages. -/
  rcv : PubInfo Tx Hash np n Hz Sch → Messages Tx Hash (Fin np) → Slot →
    History Tx Hash (Fin np) → List (Block Tx Hash (Fin np) × Sch.Sig) →
      MessagePool Tx Hash (Fin np) → AdvState → AdvOut Tx Hash np Sch.Sig × AdvState

/-- The signatures of the honest blocks of a history under the signing keys `ks`. -/
def sigTable (ks : Fin np → Sch.PK × Sch.SK) (hist : History Tx Hash (Fin np)) :
    List (Block Tx Hash (Fin np) × Sch.Sig) :=
  ((hist.map get_block).filter honest_block).map fun b => (b, Sch.sign (ks b.bid).2 b)

/-- The network accepts an adversarial message at slot `sl` when its block has a slot at most
`sl` and is baked by a corrupt party or carries a valid signature of its baker. -/
def sigOK (pks : Fin np → Sch.PK) (sl : Slot)
    (x : (Message Tx Hash (Fin np) × Sch.Sig) × DelayMap (Fin np)) : Bool :=
  decide ((get_block x.1.1).sl ≤ sl) &&
    (is_corrupt (get_block x.1.1).bid || Sch.verify (pks (get_block x.1.1).bid) (get_block x.1.1) x.1.2)

/-- The block of an adversarial message is corrupt or already in the history. -/
def histOK (hist : History Tx Hash (Fin np))
    (x : (Message Tx Hash (Fin np) × Sch.Sig) × DelayMap (Fin np)) : Bool :=
  is_corrupt (get_block x.1.1).bid || decide (get_block x.1.1 ∈ hist.map get_block)

/-- The messages the network accepts: those passing `sigOK`, and in the ideal execution also
`histOK`, without their signatures. -/
def outFilter (ideal : Bool) (pks : Fin np → Sch.PK) (sl : Slot) (hist : History Tx Hash (Fin np))
    (out : AdvOut Tx Hash np Sch.Sig) : List (Message Tx Hash (Fin np) × DelayMap (Fin np)) :=
  (out.filter fun x => sigOK pks sl x && (!ideal || histOK hist x)).map fun x => (x.1.1, x.2)

/-- The inputs of one adversary call: the delivered messages (`none` for a baking call), the
slot, the history, the message buffer and the adversarial state. -/
structure CallInput (Tx Hash : Type) (np : ℕ) (AdvState : Type) where
  /-- The delivered messages, `none` for a baking call. -/
  msgs : Option (Messages Tx Hash (Fin np))
  /-- The slot. -/
  sl : Slot
  /-- The history. -/
  hist : History Tx Hash (Fin np)
  /-- The message buffer. -/
  mb : MessagePool Tx Hash (Fin np)
  /-- The adversarial state. -/
  st : AdvState

/-- The output of the adversary on a call, given the signatures `sigTable ks` of the honest
blocks of the history. -/
def advRaw (ω : Seed Tx Hash np n Hz Sch) (A : Adversary Tx Hash np n Hz Sch)
    (c : CallInput Tx Hash np A.AdvState) : AdvOut Tx Hash np Sch.Sig × A.AdvState :=
  match c.msgs with
  | none => A.bake ω.pub c.sl c.hist (sigTable ω.ks c.hist) c.mb c.st
  | some ms => A.rcv ω.pub ms c.sl c.hist (sigTable ω.ks c.hist) c.mb c.st

/-- The execution parameters of the real (`ideal = false`) or the ideal (`ideal = true`)
execution for the seed `ω` and the adversary `A`. -/
@[instance_reducible] def mkExec (ideal : Bool) (P : Protocol Tx Hash np n Hz) (ω : Seed Tx Hash np n Hz Sch)
    (A : Adversary Tx Hash np n Hz Sch) :
    @Execution Tx Hash (Fin np) A.AdvState (ω.params P) (ω.bparams P) :=
  letI := ω.params P; letI := ω.bparams P
  { AdvState0 := A.st0
    TreeTypeMap := P.trees ω.κ ω.f
    AdversarialBake := fun sl hist mb st =>
      let r := advRaw ω A ⟨none, sl, hist, mb, st⟩
      (outFilter ideal (fun j => (ω.ks j).1) sl hist r.1, r.2)
    AdversarialRcv := fun ms sl hist mb st =>
      let r := advRaw ω A ⟨some ms, sl, hist, mb, st⟩
      (outFilter ideal (fun j => (ω.ks j).1) sl hist r.1, r.2)
    TxSelection := P.txSel }

theorem mkExec_bake (ideal : Bool) (P : Protocol Tx Hash np n Hz) (ω : Seed Tx Hash np n Hz Sch)
    (A : Adversary Tx Hash np n Hz Sch) (sl : Slot) (hist : History Tx Hash (Fin np))
    (mb : MessagePool Tx Hash (Fin np)) (st : A.AdvState) :
    (mkExec ideal P ω A).AdversarialBake sl hist mb st =
      (outFilter ideal (fun j => (ω.ks j).1) sl hist (advRaw ω A ⟨none, sl, hist, mb, st⟩).1,
        (advRaw ω A ⟨none, sl, hist, mb, st⟩).2) := rfl

theorem mkExec_rcv (ideal : Bool) (P : Protocol Tx Hash np n Hz) (ω : Seed Tx Hash np n Hz Sch)
    (A : Adversary Tx Hash np n Hz Sch) (ms : Messages Tx Hash (Fin np)) (sl : Slot)
    (hist : History Tx Hash (Fin np)) (mb : MessagePool Tx Hash (Fin np)) (st : A.AdvState) :
    (mkExec ideal P ω A).AdversarialRcv ms sl hist mb st =
      (outFilter ideal (fun j => (ω.ks j).1) sl hist (advRaw ω A ⟨some ms, sl, hist, mb, st⟩).1,
        (advRaw ω A ⟨some ms, sl, hist, mb, st⟩).2) := rfl

/-- An adversary call outputs an accepted honest block that is not in the history. -/
def Forged (ω : Seed Tx Hash np n Hz Sch) (A : Adversary Tx Hash np n Hz Sch)
    (c : CallInput Tx Hash np A.AdvState) : Prop :=
  ∃ x ∈ (advRaw ω A c).1, sigOK (fun j => (ω.ks j).1) c.sl x = true ∧ histOK c.hist x = false

/-- Without a forgery, the real and the ideal network accept the same messages. -/
theorem outFilter_eq_of_not_forged {ω : Seed Tx Hash np n Hz Sch}
    {A : Adversary Tx Hash np n Hz Sch} {c : CallInput Tx Hash np A.AdvState}
    (h : ¬Forged ω A c) :
    outFilter true (fun j => (ω.ks j).1) c.sl c.hist (advRaw ω A c).1 =
      outFilter false (fun j => (ω.ks j).1) c.sl c.hist (advRaw ω A c).1 := by
  unfold outFilter
  congr 1
  refine List.filter_congr fun x hx => ?_
  by_cases h1 : sigOK (fun j => (ω.ks j).1) c.sl x = true
  · have h2 : histOK c.hist x = true := by
      by_contra h2
      exact h ⟨x, hx, h1, by simpa using h2⟩
    simp [h1, h2]
  · simp [h1]

section Exec

variable (P : Protocol Tx Hash np n Hz) (ω : Seed Tx Hash np n Hz Sch) (A : Adversary Tx Hash np n Hz Sch)

/-- The state type of the executions of `ω` and `A`. -/
abbrev GS := @GlobalState Tx Hash (Fin np) A.AdvState (ω.params P) (ω.bparams P)

/-- The baking call of the adversary at a state. -/
def bakeCall (M : GS P ω A) : CallInput Tx Hash np A.AdvState :=
  letI := ω.params P; letI := ω.bparams P
  { msgs := none, sl := M.t_now, hist := M.history, mb := M.msg_buff, st := M.adv_state }

/-- The receiving call of the adversary for party `p` at a state. -/
def rcvCall (p : Fin np) (M : GS P ω A) : CallInput Tx Hash np A.AdvState :=
  letI := ω.params P; letI := ω.bparams P
  { msgs := some (fetch_msgs p M).1, sl := (fetch_msgs p M).2.t_now,
    hist := (fetch_msgs p M).2.history, mb := (fetch_msgs p M).2.msg_buff,
    st := (fetch_msgs p M).2.adv_state }

/-- A receiving step of a party in the real (`ideal = false`) or the ideal execution. -/
def sRcv (ideal : Bool) (p : Fin np) (M : GS P ω A) : GS P ω A :=
  letI := ω.params P; letI := ω.bparams P; letI := mkExec ideal P ω A
  party_rcv_step_world p M

/-- A baking step of a party in the real (`ideal = false`) or the ideal execution. -/
def sBake (ideal : Bool) (p : Fin np) (M : GS P ω A) : GS P ω A :=
  letI := ω.params P; letI := ω.bparams P; letI := mkExec ideal P ω A
  party_bake_step_world p M

/-- One phase of the real (`ideal = false`) or the ideal execution. -/
def sPhase (ideal : Bool) (M : GS P ω A) : GS P ω A :=
  letI := ω.params P; letI := ω.bparams P; letI := mkExec ideal P ω A
  phaseStep M

/-- The trace of the real (`ideal = false`) or the ideal execution. -/
def sTrace (ideal : Bool) (k : ℕ) : GS P ω A :=
  letI := ω.params P; letI := ω.bparams P; letI := mkExec ideal P ω A
  runTrace A.AdvState k

/-- The adversary call of a party step at a state, if there is one: the party is corrupt and
has a local state. -/
def stepCalls (bake : Bool) (c : Fin np × GS P ω A) : List (CallInput Tx Hash np A.AdvState) :=
  letI := ω.params P; letI := ω.bparams P
  if (c.2.state_map c.1).isSome && is_corrupt c.1 then
    [if bake then bakeCall P ω A c.2 else rcvCall P ω A c.1 c.2] else []

/-- The adversary calls of one phase of the real execution, from the state `N`. -/
def phaseCalls (N : GS P ω A) : List (CallInput Tx Hash np A.AdvState) :=
  letI := ω.params P; letI := ω.bparams P
  match N.progress with
  | .Ready => (foldrCalls (sRcv P ω A false) N N.exec_order).flatMap (stepCalls P ω A false)
  | .Delivered => (foldrCalls (sBake P ω A false) N N.exec_order).flatMap (stepCalls P ω A true)
  | .Baked => []

/-- The adversary calls of the first `K` phases of the real execution. -/
def traceCalls (K : ℕ) : List (CallInput Tx Hash np A.AdvState) :=
  (List.range K).flatMap fun k => phaseCalls P ω A (sTrace P ω A false k)

/-- **The forging event.** Some adversary call in the first `K` phases of the real execution
outputs an accepted honest block that is not in the history. -/
def Forge (K : ℕ) : Prop := ∃ c ∈ traceCalls P ω A K, Forged ω A c

theorem sRcv_eq (p : Fin np) (M : GS P ω A)
    (h : ∀ c ∈ stepCalls P ω A false (p, M), ¬Forged ω A c) :
    sRcv P ω A true p M = sRcv P ω A false p M := by
  let _ := ω.params P; let _ := ω.bparams P
  unfold sRcv party_rcv_step_world
  unfold stepCalls at h
  cases hs : M.state_map p with
  | none => rfl
  | some l =>
    by_cases hc : is_corrupt p
    · have h' := outFilter_eq_of_not_forged (h (rcvCall P ω A p M) (by simp [hs, hc]))
      simp only [hc, Bool.not_true, Bool.false_eq_true, if_false]
      have e : ∀ ms sl hist mb st, (ms, sl, hist, mb, st) = ((fetch_msgs p M).1,
          (fetch_msgs p M).2.t_now, (fetch_msgs p M).2.history, (fetch_msgs p M).2.msg_buff,
          (fetch_msgs p M).2.adv_state) →
          (mkExec true P ω A).AdversarialRcv ms sl hist mb st =
            (mkExec false P ω A).AdversarialRcv ms sl hist mb st := by
        intro ms sl hist mb st he
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := he
        rw [mkExec_rcv, mkExec_rcv]
        exact congrArg (·, _) h'
      rw [e _ _ _ _ _ rfl]
    · simp only [hc]
      rfl

theorem sBake_eq (p : Fin np) (M : GS P ω A)
    (h : ∀ c ∈ stepCalls P ω A true (p, M), ¬Forged ω A c) :
    sBake P ω A true p M = sBake P ω A false p M := by
  let _ := ω.params P; let _ := ω.bparams P
  unfold sBake party_bake_step_world
  unfold stepCalls at h
  cases hs : M.state_map p with
  | none => rfl
  | some l =>
    by_cases hc : is_corrupt p
    · have h' := outFilter_eq_of_not_forged (h (bakeCall P ω A M) (by simp [hs, hc]))
      simp only [hc, Bool.not_true, Bool.false_eq_true, if_false]
      have e : (mkExec true P ω A).AdversarialBake M.t_now M.history M.msg_buff M.adv_state =
          (mkExec false P ω A).AdversarialBake M.t_now M.history M.msg_buff M.adv_state := by
        rw [mkExec_bake, mkExec_bake]
        exact congrArg (·, _) h'
      rw [e]
    · simp only [hc]
      rfl

theorem sPhase_def (ideal : Bool) (N : GS P ω A) :
    sPhase P ω A ideal N = (letI := ω.params P; letI := ω.bparams P
      match N.progress with
      | .Ready => { N.exec_order.foldr (sRcv P ω A ideal) N with progress := .Delivered }
      | .Delivered => { N.exec_order.foldr (sBake P ω A ideal) N with progress := .Baked }
      | .Baked => { inc_round (round_tick N) with progress := .Ready }) := rfl

/-- Without a forgery in a phase, the real and the ideal phase coincide. -/
theorem sPhase_eq (N : GS P ω A) (h : ∀ c ∈ phaseCalls P ω A N, ¬Forged ω A c) :
    sPhase P ω A true N = sPhase P ω A false N := by
  let _ := ω.params P; let _ := ω.bparams P
  rw [sPhase_def, sPhase_def]
  unfold phaseCalls at h
  cases hp : N.progress with
  | Ready =>
    rw [hp] at h
    dsimp only at h ⊢
    rw [foldr_congr_calls (sRcv P ω A false) (sRcv P ω A true) N N.exec_order
      fun c hc => sRcv_eq P ω A c.1 c.2 fun c' hc' => h c' (List.mem_flatMap.2 ⟨c, hc, hc'⟩)]
  | Delivered =>
    rw [hp] at h
    dsimp only at h ⊢
    rw [foldr_congr_calls (sBake P ω A false) (sBake P ω A true) N N.exec_order
      fun c hc => sBake_eq P ω A c.1 c.2 fun c' hc' => h c' (List.mem_flatMap.2 ⟨c, hc, hc'⟩)]
  | Baked => rfl

theorem sTrace_succ (ideal : Bool) (k : ℕ) :
    sTrace P ω A ideal (k + 1) = sPhase P ω A ideal (sTrace P ω A ideal k) :=
  letI := ω.params P; letI := ω.bparams P; letI := mkExec ideal P ω A
  runTrace_succ k

/-- **Identical until forgery.** If no adversary call of the first `K` phases of the real
execution is a forgery, the real and the ideal traces coincide up to phase `K`. -/
theorem sTrace_ideal_eq {K : ℕ} (h : ¬Forge P ω A K) :
    ∀ k ≤ K, sTrace P ω A true k = sTrace P ω A false k := by
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [sTrace_succ, sTrace_succ, ih (by omega)]
    refine sPhase_eq P ω A _ fun c hc hf => h ⟨c, ?_, hf⟩
    exact List.mem_flatMap.2 ⟨k, List.mem_range.2 (by omega), hc⟩

/-- The blocks accepted by the network have a slot at most the current slot. -/
theorem outFilter_sl {ideal : Bool} {pks : Fin np → Sch.PK} {sl : Slot}
    {hist : History Tx Hash (Fin np)} {out : AdvOut Tx Hash np Sch.Sig}
    {m : Message Tx Hash (Fin np)} (hm : m ∈ (outFilter ideal pks sl hist out).map Prod.fst) :
    (get_block m).sl ≤ sl := by
  simp only [outFilter, List.map_map, List.mem_map, List.mem_filter, Function.comp_apply] at hm
  obtain ⟨x, ⟨_, hx⟩, rfl⟩ := hm
  simp only [sigOK, Bool.and_eq_true, decide_eq_true_eq] at hx
  exact hx.1.1

/-- The honest blocks accepted by the ideal network are in the history. -/
theorem outFilter_ideal_hist {pks : Fin np → Sch.PK} {sl : Slot}
    {hist : History Tx Hash (Fin np)} {out : AdvOut Tx Hash np Sch.Sig} :
    honest_subset ((outFilter true pks sl hist out).map fun mp => get_block mp.1)
      (hist.map get_block) := by
  intro b hb hh
  simp only [outFilter, List.map_map, List.mem_map, List.mem_filter, Function.comp_apply] at hb
  obtain ⟨x, ⟨_, hx⟩, rfl⟩ := hb
  simp only [histOK, Bool.and_eq_true, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    decide_eq_true_eq] at hx
  rcases hx.2 with hc | hm
  · simp [honest_block, is_honest, is_corrupt] at hh hc
    rw [hh] at hc
    exact absurd hc (by decide)
  · exact hm

/-- **The ideal execution is forging free**: in every state, the adversary of the ideal
execution sends no honest block outside the history. -/
theorem forging_free_ideal (N : GS P ω A) :
    letI := ω.params P; letI := ω.bparams P; letI := mkExec true P ω A
    forging_free N := by
  let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec true P ω A
  refine ⟨fun N1 _ p => ?_, fun N1 _ => ?_⟩
  · rw [mkExec_rcv]; exact outFilter_ideal_hist
  · rw [mkExec_bake]; exact outFilter_ideal_hist

/-- The blocks of the history have slots at most the current slot. -/
def SlotsBounded (M : GS P ω A) : Prop :=
  letI := ω.params P; letI := ω.bparams P
  ∀ m ∈ M.history, (get_block m).sl ≤ M.t_now

theorem sRcv_slots (p : Fin np) (M : GS P ω A) (h : SlotsBounded P ω A M) :
    SlotsBounded P ω A (sRcv P ω A false p M) := by
  let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec false P ω A
  intro m hm
  simp only [sRcv] at hm ⊢
  rw [rcv_t_now]
  rcases (rcv_history M p m).1 hm with hm | ⟨_, _, hm⟩
  · exact h m hm
  · rw [mkExec_rcv] at hm
    exact outFilter_sl hm

theorem sBake_slots (p : Fin np) (M : GS P ω A) (h : SlotsBounded P ω A M) :
    SlotsBounded P ω A (sBake P ω A false p M) := by
  let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec false P ω A
  intro m hm
  simp only [sBake] at hm ⊢
  rw [bake_t_now]
  rcases (bake_history M p m).1 hm with hm | ⟨l, _, ⟨_, hm⟩ | ⟨_, hm⟩⟩
  · exact h m hm
  · rw [honest_bake_eq] at hm
    split_ifs at hm
    · simp only [List.mem_singleton] at hm; subst hm; rfl
    · simp at hm
  · rw [mkExec_bake] at hm
    exact outFilter_sl hm

theorem foldr_slots (g : Fin np → GS P ω A → GS P ω A)
    (hg : ∀ p M, SlotsBounded P ω A M → SlotsBounded P ω A (g p M)) (M : GS P ω A)
    (h : SlotsBounded P ω A M) (l : List (Fin np)) : SlotsBounded P ω A (l.foldr g M) := by
  induction l with
  | nil => exact h
  | cons p ps ih => exact hg p _ ih

/-- **Slots of broadcast blocks.** In the real execution, every broadcast block has a slot at
most the current slot. -/
theorem sTrace_slots (k : ℕ) : SlotsBounded P ω A (sTrace P ω A false k) := by
  induction k with
  | zero => intro m hm; simp [sTrace, runTrace, N0] at hm
  | succ k ih =>
    rw [sTrace_succ, sPhase_def]
    let _ := ω.params P; let _ := ω.bparams P
    cases (sTrace P ω A false k).progress with
    | Ready =>
      have := foldr_slots P ω A _ (sRcv_slots P ω A) _ ih (sTrace P ω A false k).exec_order
      exact this
    | Delivered =>
      have := foldr_slots P ω A _ (sBake_slots P ω A) _ ih (sTrace P ω A false k).exec_order
      exact this
    | Baked =>
      intro m hm
      have := ih m hm
      simp only [inc_round, round_tick] at this ⊢
      omega

end Exec

end Signed

end CatCryptCore.Consensus.PoSNSB
