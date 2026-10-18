/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.PoSNSB.Prob.Collision
public import CatCryptCore.Crypto.OracleAdversaryTimed

/-!
# PoS-NSB: running time of the two reductions

The security theorem `pos_nsb_security` reduces to the EUF-CMA advantage of the forgers
`forger Sch P A H cd μ W K i` and to the collision-search advantage of
`collFinder Sch P A H cd μ W K`. Both reductions are given here as costed trees of
`OracleAdv.Timed` (`CatCryptCore/Crypto/OracleAdversaryTimed.lean`), with the theorems that
erasing the step costs gives the reductions and the bounds on their time.

The adversary `A` is a structure of functions, not a tree: each of its calls is charged the
per-call cost `cost.adv`. Its outputs are bounded in length (`Adversary.OutputBound A ℓ`),
so that every party step adds at most `ℓ + 1` messages to the history; with
`m = P.IP.length` parties, the history after `j` phases has at most `j * (m * (ℓ + 1))`
messages (`HistBound`).

## Cost model

The registered costs of `OracleAdversaryTimed`: one unit per `rand` and per `query` node.
The trusted base is the cost record `ReductionCost`:

* `adv` — one call of the adversary on its inputs;
* `sign` — one signature with a known signing key (signing for the parties other than the
  target party, and the signature table of the real execution);
* `find` — the search of one adversary output for a forgery of the target party;
* `step` — one party step of the protocol besides the adversary call: honest baking and
  receiving (lottery evaluation, hashing of the parent block, tree update), the acceptance
  filter of the network and the network update;
* `phase` — the transition between two phases;
* `pair` — one pair of the collision search: two hash evaluations and the comparisons.

## Main definitions

* `ReductionCost`, `Adversary.OutputBound`, `HistBound`
* `forger.timed` — the costed forger; `collFinder.timed` — the costed collision finder
* `stepCost`, `phaseCost` — the costs of one simulated party step and of one phase

## Main results

* `forger.erase_timed` — `(forger.timed …).erase = forger …`
* `forger.timeBound_timed` — time at most `2 + K * phaseCost cost m (K * (m * (ℓ + 1)))`:
  at most `K * m` adversary calls of cost `adv + find + step`, at most one signing query or
  local signature (cost `1 + sign`) per honest block of the history of each call, the phase
  transitions, the sample of the seed and the final query
* `collFinder.erase_timed`, `collFinder.run_erase_timed` — erasure gives the coins and the
  output of `collFinder`
* `collFinder.timeBound_timed` — time at most `1 + execBound cost m ℓ K + B * B * pair`
  with `B = 1 + K * (m * (ℓ + 1))` blocks searched; `execWork_le` bounds the charged work of
  the real execution by `execBound`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace CatCryptCore.Consensus.PoSNSB

open Parameters BlockParameters Corruption Execution
open CatCrypt.Crypto CatCrypt.Crypto.Signatures CatCrypt.Crypto.Assumptions

/-! ## Step-prefixed sequencing -/

section StepBind

variable {D R α β γ : Type}

/-- The step-prefixed tree `x` followed by `f` on its output: the step cost of `x` precedes
the sequenced tree. -/
def stepBind (x : ℕ × OracleAdv.Timed D R α) (f : α → ℕ × OracleAdv.Timed D R β) :
    ℕ × OracleAdv.Timed D R β :=
  OracleAdv.Timed.delay x.1 (x.2.bind f)

theorem erase_stepBind (x : ℕ × OracleAdv.Timed D R α) (f : α → ℕ × OracleAdv.Timed D R β) :
    (stepBind x f).2.erase = x.2.erase.bind fun a => (f a).2.erase :=
  OracleAdv.Timed.erase_bind x.2 f

theorem stepTimeBound_stepBind {x : ℕ × OracleAdv.Timed D R α}
    {f : α → ℕ × OracleAdv.Timed D R β} {m n : ℕ} (hx : OracleAdv.Timed.StepTimeBound x m)
    (hf : ∀ a, OracleAdv.Timed.StepTimeBound (f a) n) :
    OracleAdv.Timed.StepTimeBound (stepBind x f) (m + n) :=
  (OracleAdv.Timed.stepTimeBound_delay (c := x.1) (OracleAdv.Timed.timeBound_bind hx.2 hf)).mono
    (by have := hx.1; omega)

theorem stepTimeBound_ret (a : α) (n : ℕ) :
    OracleAdv.Timed.StepTimeBound ((0, .ret a) : ℕ × OracleAdv.Timed D R α) n :=
  ⟨Nat.zero_le n, trivial⟩

/-- The costed form of `mapQ`: run the step-prefixed program `g` on every element. -/
def mapQ.timed (g : β → ℕ × OracleAdv.Timed D R γ) :
    List β → ℕ × OracleAdv.Timed D R (List γ)
  | [] => (0, .ret [])
  | b :: bs => stepBind (g b) fun x => stepBind (mapQ.timed g bs) fun xs => (0, .ret (x :: xs))

theorem mapQ.erase_timed (g : β → ℕ × OracleAdv.Timed D R γ) (l : List β) :
    (mapQ.timed g l).2.erase = mapQ (fun b => (g b).2.erase) l := by
  induction l with
  | nil => rfl
  | cons b bs ih => simp only [mapQ.timed, mapQ, erase_stepBind, ih]; rfl

theorem mapQ.stepTimeBound_timed {g : β → ℕ × OracleAdv.Timed D R γ} {t : ℕ}
    (hg : ∀ b, OracleAdv.Timed.StepTimeBound (g b) t) (l : List β) :
    OracleAdv.Timed.StepTimeBound (mapQ.timed g l) (l.length * t) := by
  induction l with
  | nil => exact stepTimeBound_ret _ _
  | cons b bs ih =>
    refine (stepTimeBound_stepBind (hg b) fun x =>
      stepTimeBound_stepBind ih fun xs => stepTimeBound_ret _ 0).mono ?_
    simp only [List.length_cons, Nat.succ_mul]
    omega

end StepBind

/-! ## Costs and the adversary -/

/-- The cost parameters of the reductions: the trusted base of the time statements. -/
structure ReductionCost where
  /-- One call of the adversary on its inputs. -/
  adv : ℕ
  /-- One signature with a known signing key. -/
  sign : ℕ
  /-- The search of one adversary output for a forgery of the target party. -/
  find : ℕ
  /-- One party step of the protocol besides the adversary call. -/
  step : ℕ
  /-- The transition between two phases. -/
  phase : ℕ
  /-- One pair of the collision search. -/
  pair : ℕ

/-- The cost of one simulated party step when the history has at most `h` messages: one
entry of the signature table per message, the adversary call, the forgery search and the
step of the protocol. -/
def stepCost (cost : ReductionCost) (h : ℕ) : ℕ :=
  h * (1 + cost.sign) + (cost.adv + (cost.find + cost.step))

/-- The cost of one phase of `m` party steps when the history has at most `h` messages. -/
def phaseCost (cost : ReductionCost) (m h : ℕ) : ℕ :=
  cost.phase + m * stepCost cost h

theorem stepCost_mono (cost : ReductionCost) {h h' : ℕ} (hh : h ≤ h') :
    stepCost cost h ≤ stepCost cost h' := by
  unfold stepCost
  have := Nat.mul_le_mul_right (1 + cost.sign) hh
  omega

theorem phaseCost_mono (cost : ReductionCost) (m : ℕ) {h h' : ℕ} (hh : h ≤ h') :
    phaseCost cost m h ≤ phaseCost cost m h' := by
  unfold phaseCost
  have := Nat.mul_le_mul_left m (stepCost_mono cost hh)
  omega

section Network

variable {Tx Hash Party AdvState : Type} [Parameters Party] [BlockParameters Tx Hash Party]

theorem honest_bake_length (sl : Slot) (txs : Tx) (l : LocalState Tx Hash Party) :
    (honest_bake sl txs l).1.length ≤ 1 := by
  unfold honest_bake
  simp only [State.bind, State.get]
  by_cases hw : Winner l.pk sl <;> simp [hw, State.bind, State.modify, State.pure]

end Network

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ} {PK SK Sig : Type}

/-- The adversary outputs at most `ℓ` messages per call. -/
def Adversary.OutputBound (A : Adversary Tx Hash np n Hz PK Sig) (ℓ : ℕ) : Prop :=
  (∀ pub sl hist tbl mb st, (A.bake pub sl hist tbl mb st).1.length ≤ ℓ) ∧
    ∀ pub ms sl hist tbl mb st, (A.rcv pub ms sl hist tbl mb st).1.length ≤ ℓ

theorem outFilter_length_le (Sch : PSigScheme (Block Tx Hash (Fin np)) PK SK Sig)
    (ideal : Bool) (pks : Fin np → PK) (sl : Slot) (hist : History Tx Hash (Fin np))
    (out : AdvOut Tx Hash np Sig) : (outFilter Sch ideal pks sl hist out).length ≤ out.length := by
  simpa [outFilter] using List.length_filter_le _ out

/-! ## The history bound -/

section History

variable (Sch : PSigScheme (Block Tx Hash (Fin np)) PK SK Sig) [hS : Sch.Deterministic]
  (P : Protocol Tx Hash np n Hz) (A : Adversary Tx Hash np n Hz PK Sig)
  (ω : Seed Tx Hash np n Hz PK SK)

/-- The state `M` executes the initial parties and its history has at most `h` messages. -/
def HistBound (h : ℕ) (M : GS P ω A) : Prop :=
  letI := ω.params P; letI := ω.bparams P
  M.exec_order = P.IP ∧ M.history.length ≤ h

variable {P A ω}

theorem HistBound.mono {h h' : ℕ} {M : GS P ω A} (hM : HistBound P A ω h M) (hh : h ≤ h') :
    HistBound P A ω h' M :=
  ⟨hM.1, hM.2.trans hh⟩

variable (P A ω)

theorem histBound_sTrace_zero (ideal : Bool) : HistBound P A ω 0 (sTrace Sch P ω A ideal 0) := by
  refine ⟨rfl, ?_⟩
  simp [sTrace, runTrace, N0]

variable {ℓ : ℕ} (hA : A.OutputBound ℓ)
include hA

theorem histBound_sRcv (ideal : Bool) (p : Fin np) {h : ℕ} {M : GS P ω A}
    (hM : HistBound P A ω h M) : HistBound P A ω (h + (ℓ + 1)) (sRcv Sch P ω A ideal p M) := by
  let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec Sch ideal P ω A
  unfold sRcv party_rcv_step_world
  cases hl : M.state_map p with
  | none => exact hM.mono (by omega)
  | some l =>
    by_cases hc : is_corrupt p
    · simp only [hc, Bool.not_true, Bool.false_eq_true, if_false]
      refine ⟨?_, ?_⟩
      · simpa [flood_msgs_adv_exec_order, fetch_msgs, rmv_zero_msgs] using hM.1
      · have h1 := outFilter_length_le Sch ideal (fun j => (ω.ks j).1)
          (fetch_msgs p M).2.t_now (fetch_msgs p M).2.history (advRaw Sch ω A ⟨some (fetch_msgs p M).1, (fetch_msgs p M).2.t_now,
            (fetch_msgs p M).2.history, (fetch_msgs p M).2.msg_buff,
            (fetch_msgs p M).2.adv_state⟩).1
        have h2 := hA.2 ω.pub (fetch_msgs p M).1 (fetch_msgs p M).2.t_now
          (fetch_msgs p M).2.history (sigTable Sch ω.ks (fetch_msgs p M).2.history)
          (fetch_msgs p M).2.msg_buff (fetch_msgs p M).2.adv_state
        have h3 := hM.2
        simp only [flood_msgs_adv_history, List.length_append, List.length_map, mkExec_rcv]
        simp only [advRaw] at h1 ⊢
        simp only [fetch_msgs, rmv_zero_msgs] at h1 h2 ⊢
        omega
    · simp only [hc, Bool.not_false, if_true]
      exact ⟨by simpa [upd_local, fetch_msgs, rmv_zero_msgs] using hM.1,
        by simpa [upd_local, fetch_msgs, rmv_zero_msgs] using hM.2.trans (by omega)⟩

theorem histBound_sBake (ideal : Bool) (p : Fin np) {h : ℕ} {M : GS P ω A}
    (hM : HistBound P A ω h M) : HistBound P A ω (h + (ℓ + 1)) (sBake Sch P ω A ideal p M) := by
  let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec Sch ideal P ω A
  unfold sBake party_bake_step_world
  cases hl : M.state_map p with
  | none => exact hM.mono (by omega)
  | some l =>
    by_cases hc : is_corrupt p
    · simp only [hc, Bool.not_true, Bool.false_eq_true, if_false]
      refine ⟨by simpa [flood_msgs_adv_exec_order] using hM.1, ?_⟩
      have h1 := outFilter_length_le Sch ideal (fun j => (ω.ks j).1) M.t_now M.history
        (advRaw Sch ω A ⟨none, M.t_now, M.history, M.msg_buff, M.adv_state⟩).1
      have h2 := hA.1 ω.pub M.t_now M.history (sigTable Sch ω.ks M.history) M.msg_buff
        M.adv_state
      have h3 := hM.2
      simp only [flood_msgs_adv_history, List.length_append, List.length_map, mkExec_bake]
      simp only [advRaw] at h1 ⊢
      omega
    · simp only [hc, Bool.not_false, if_true]
      have h1 := honest_bake_length M.t_now
        (TxSelection (Hash := Hash) (AdvState := A.AdvState) M.t_now p) l
      have h3 := hM.2
      refine ⟨by simpa [flood_msgs_exec_order, upd_local] using hM.1, ?_⟩
      simp only [flood_msgs_history, List.length_append, upd_local]
      omega

theorem histBound_sStep (bake : Bool) (p : Fin np) {h : ℕ} {M : GS P ω A}
    (hM : HistBound P A ω h M) :
    HistBound P A ω (h + (ℓ + 1)) (sStep Sch P A ω bake p M) := by
  cases bake
  · exact histBound_sRcv Sch P A ω hA false p hM
  · exact histBound_sBake Sch P A ω hA false p hM

theorem histBound_foldr (g : Fin np → GS P ω A → GS P ω A)
    (hg : ∀ p {h : ℕ} {M : GS P ω A}, HistBound P A ω h M → HistBound P A ω (h + (ℓ + 1)) (g p M))
    {h : ℕ} {N : GS P ω A} (hN : HistBound P A ω h N) (l : List (Fin np)) :
    HistBound P A ω (h + l.length * (ℓ + 1)) (l.foldr g N) := by
  induction l with
  | nil => simpa using hN
  | cons p ps ih =>
    refine (hg p ih).mono ?_
    simp only [List.length_cons, Nat.succ_mul]
    omega

theorem histBound_sPhase {h : ℕ} {N : GS P ω A} (hN : HistBound P A ω h N) :
    HistBound P A ω (h + P.IP.length * (ℓ + 1)) (sPhase Sch P ω A false N) := by
  let _ := ω.params P; let _ := ω.bparams P
  rw [sPhase_def]
  have hl : N.exec_order.length = P.IP.length := by rw [hN.1]
  split
  · have := histBound_foldr P A ω hA (sRcv Sch P ω A false)
      (fun p _ _ hM => histBound_sRcv Sch P A ω hA false p hM) hN N.exec_order
    rw [hl] at this
    exact this
  · have := histBound_foldr P A ω hA (sBake Sch P ω A false)
      (fun p _ _ hM => histBound_sBake Sch P A ω hA false p hM) hN N.exec_order
    rw [hl] at this
    exact this
  · exact hN.mono (by omega)

theorem histBound_sTrace (K : ℕ) :
    HistBound P A ω (K * (P.IP.length * (ℓ + 1))) (sTrace Sch P ω A false K) := by
  induction K with
  | zero => simpa using histBound_sTrace_zero Sch P A ω false
  | succ K ih =>
    rw [sTrace_succ]
    refine (histBound_sPhase Sch P A ω hA ih).mono ?_
    rw [Nat.succ_mul]

end History

/-! ## The costed forger -/

/-- The costed programs of the forger. -/
abbrev FProg.Timed (Tx Hash : Type) (np : ℕ) (Sig : Type) :=
  OracleAdv.Timed (Block Tx Hash (Fin np)) Sig (Block Tx Hash (Fin np) × Sig)

section Forger

variable (Sch : PSigScheme (Block Tx Hash (Fin np)) PK SK Sig) [hS : Sch.Deterministic]
  (P : Protocol Tx Hash np n Hz) (A : Adversary Tx Hash np n Hz PK Sig) (cost : ReductionCost)
  (i : Fin np) (pk : PK) (ω : Seed Tx Hash np n Hz PK SK)

/-- The costed signature of a block in the simulation: a signing query for party `i`, a
local signature at cost `cost.sign` for the other parties. -/
def simSign.timed (b : Block Tx Hash (Fin np)) :
    ℕ × OracleAdv.Timed (Block Tx Hash (Fin np)) Sig (Block Tx Hash (Fin np) × Sig) :=
  if b.bid = i then (0, .query b (fun _ => 0) fun σ => .ret (b, σ))
  else (cost.sign, .ret (b, hS.dsign (ω.ks b.bid).2 b))

theorem simSign.erase_timed (b : Block Tx Hash (Fin np)) :
    (simSign.timed Sch cost i ω b).2.erase = simSign Sch i ω b := by
  unfold simSign.timed simSign
  split <;> rfl

theorem simSign.stepTimeBound_timed (b : Block Tx Hash (Fin np)) :
    OracleAdv.Timed.StepTimeBound (simSign.timed Sch cost i ω b) (1 + cost.sign) := by
  unfold simSign.timed
  split
  · exact ⟨Nat.zero_le _, by omega, fun _ => ⟨Nat.zero_le _, trivial⟩⟩
  · exact ⟨by omega, trivial⟩

/-- The costed signature table of a history in the simulation. -/
def simTable.timed (hist : History Tx Hash (Fin np)) :
    ℕ × OracleAdv.Timed (Block Tx Hash (Fin np)) Sig (List (Block Tx Hash (Fin np) × Sig)) :=
  mapQ.timed (simSign.timed Sch cost i ω) ((hist.map get_block).filter honest_block)

theorem simTable.erase_timed (hist : History Tx Hash (Fin np)) :
    (simTable.timed Sch cost i ω hist).2.erase = simTable Sch i ω hist := by
  simp only [simTable.timed, simTable, mapQ.erase_timed, simSign.erase_timed]

theorem simTable.stepTimeBound_timed (hist : History Tx Hash (Fin np)) :
    OracleAdv.Timed.StepTimeBound (simTable.timed Sch cost i ω hist)
      (hist.length * (1 + cost.sign)) := by
  refine (mapQ.stepTimeBound_timed (simSign.stepTimeBound_timed Sch cost i ω) _).mono ?_
  refine Nat.mul_le_mul_right _ ?_
  simpa using List.length_filter_le honest_block (hist.map get_block)

/-- The costed adversary call of the simulation, continued by `f` on the output of the
adversary: the signature table, then the adversary at cost `cost.adv`. -/
def simCall.timed (c : CallInput Tx Hash np A.AdvState)
    (f : AdvOut Tx Hash np Sig × A.AdvState → ℕ × FProg.Timed Tx Hash np Sig) :
    ℕ × FProg.Timed Tx Hash np Sig :=
  stepBind (simTable.timed Sch cost i ω c.hist) fun tbl =>
    OracleAdv.Timed.delay cost.adv (f (match c.msgs with
      | none => A.bake (simPub i pk ω) c.sl c.hist tbl c.mb c.st
      | some ms => A.rcv (simPub i pk ω) ms c.sl c.hist tbl c.mb c.st))

theorem simCall.erase_timed (c : CallInput Tx Hash np A.AdvState)
    (f : AdvOut Tx Hash np Sig × A.AdvState → ℕ × FProg.Timed Tx Hash np Sig) :
    (simCall.timed Sch A cost i pk ω c f).2.erase =
      (simAdv Sch A i pk ω c).bind fun r => (f r).2.erase := by
  simp only [simCall.timed, simAdv, erase_stepBind, simTable.erase_timed, OracleAdv.bind_assoc]
  rfl

theorem simCall.stepTimeBound_timed {ℓ : ℕ} (hA : A.OutputBound ℓ)
    (c : CallInput Tx Hash np A.AdvState)
    {f : AdvOut Tx Hash np Sig × A.AdvState → ℕ × FProg.Timed Tx Hash np Sig} {t : ℕ}
    (hf : ∀ r, r.1.length ≤ ℓ → OracleAdv.Timed.StepTimeBound (f r) t) :
    OracleAdv.Timed.StepTimeBound (simCall.timed Sch A cost i pk ω c f)
      (c.hist.length * (1 + cost.sign) + (cost.adv + t)) :=
  stepTimeBound_stepBind (simTable.stepTimeBound_timed Sch cost i ω c.hist) fun tbl =>
    OracleAdv.Timed.stepTimeBound_delay (hf _ (by
      split
      · exact hA.1 _ _ _ _ _ _
      · exact hA.2 _ _ _ _ _ _ _))

theorem stepCall_hist (bake : Bool) (p : Fin np) (M : GS P ω A) :
    letI := ω.params P; letI := ω.bparams P
    (stepCall P A ω bake p M).hist = M.history := by
  cases bake <;> rfl

/-- The costed party step of the simulation, continued by `k` on the next state. -/
def simStep.timed (bake : Bool) (p : Fin np) (M : GS P ω A)
    (k : GS P ω A → ℕ × FProg.Timed Tx Hash np Sig) : ℕ × FProg.Timed Tx Hash np Sig :=
  letI := ω.params P; letI := ω.bparams P
  if (M.state_map p).isSome && is_corrupt p then
    simCall.timed Sch A cost i pk ω (stepCall P A ω bake p M) fun r =>
      match findForgery Sch i (simPks i pk ω) (stepCall P A ω bake p M) r.1 with
      | some fg => (cost.find, .ret fg)
      | none => OracleAdv.Timed.delay (cost.find + cost.step)
          (k (corruptStep Sch P A i pk ω bake p M r))
  else OracleAdv.Timed.delay cost.step (k (sStep Sch P A ω bake p M))

theorem simStep.erase_timed (bake : Bool) (p : Fin np) (M : GS P ω A)
    (k : GS P ω A → ℕ × FProg.Timed Tx Hash np Sig) :
    (simStep.timed Sch P A cost i pk ω bake p M k).2.erase =
      simStep Sch P A i pk ω bake p M fun M' => (k M').2.erase := by
  unfold simStep.timed simStep
  split
  · rw [simCall.erase_timed]
    congr 1
    funext r
    cases findForgery Sch i (simPks i pk ω) (stepCall P A ω bake p M) r.1 <;> rfl
  · rfl

/-- The costed steps of a list of parties in the simulation, continued by `k`. -/
def simFold.timed (bake : Bool) (N : GS P ω A) :
    List (Fin np) → (GS P ω A → ℕ × FProg.Timed Tx Hash np Sig) →
      ℕ × FProg.Timed Tx Hash np Sig
  | [], k => k N
  | p :: ps, k => simFold.timed bake N ps fun M => simStep.timed Sch P A cost i pk ω bake p M k

theorem simFold.erase_timed (bake : Bool) (N : GS P ω A) (l : List (Fin np))
    (k : GS P ω A → ℕ × FProg.Timed Tx Hash np Sig) :
    (simFold.timed Sch P A cost i pk ω bake N l k).2.erase =
      simFold Sch P A i pk ω bake N l fun M => (k M).2.erase := by
  induction l generalizing k with
  | nil => rfl
  | cons p ps ih =>
    simp only [simFold.timed, simFold, ih, simStep.erase_timed]

/-- The costed phase of the simulation, continued by `k`: the phase transition at cost
`cost.phase`, then the party steps. -/
def simPhase.timed (N : GS P ω A) (k : GS P ω A → ℕ × FProg.Timed Tx Hash np Sig) :
    ℕ × FProg.Timed Tx Hash np Sig :=
  letI := ω.params P; letI := ω.bparams P
  match N.progress with
  | .Ready => OracleAdv.Timed.delay cost.phase
      (simFold.timed Sch P A cost i pk ω false N N.exec_order fun M =>
        k { M with progress := .Delivered })
  | .Delivered => OracleAdv.Timed.delay cost.phase
      (simFold.timed Sch P A cost i pk ω true N N.exec_order fun M =>
        k { M with progress := .Baked })
  | .Baked => OracleAdv.Timed.delay cost.phase
      (k { inc_round (round_tick N) with progress := .Ready })

theorem simPhase.erase_timed (N : GS P ω A) (k : GS P ω A → ℕ × FProg.Timed Tx Hash np Sig) :
    (simPhase.timed Sch P A cost i pk ω N k).2.erase =
      simPhase Sch P A i pk ω N fun M => (k M).2.erase := by
  let _ := ω.params P; let _ := ω.bparams P
  unfold simPhase.timed simPhase
  cases N.progress <;> simp only [OracleAdv.Timed.delay, simFold.erase_timed]

/-- The costed first `j` phases of the simulation, continued by `k`. -/
def simTrace.timed : ℕ → (GS P ω A → ℕ × FProg.Timed Tx Hash np Sig) →
    ℕ × FProg.Timed Tx Hash np Sig
  | 0, k => k (sTrace Sch P ω A false 0)
  | j + 1, k => simTrace.timed j fun M => simPhase.timed Sch P A cost i pk ω M k

theorem simTrace.erase_timed (j : ℕ) (k : GS P ω A → ℕ × FProg.Timed Tx Hash np Sig) :
    (simTrace.timed Sch P A cost i pk ω j k).2.erase =
      simTrace Sch P A i pk ω j fun M => (k M).2.erase := by
  induction j generalizing k with
  | zero => rfl
  | succ j ih => simp only [simTrace.timed, simTrace, ih, simPhase.erase_timed]

/-- The costed program of the forger: the simulation of `K` phases, then the query of the
genesis block. -/
def forgerProg.timed (K : ℕ) : ℕ × FProg.Timed Tx Hash np Sig :=
  simTrace.timed Sch P A cost i pk ω K fun _ =>
    (0, .query P.GB (fun _ => 0) fun σ => .ret (P.GB, σ))

theorem forgerProg.erase_timed (K : ℕ) :
    (forgerProg.timed Sch P A cost i pk ω K).2.erase = forgerProg Sch P A i pk ω K := by
  simp only [forgerProg.timed, forgerProg, simTrace.erase_timed]
  rfl

/-! ### Time of the simulation -/

variable {ℓ : ℕ} (hA : A.OutputBound ℓ)
include hA

theorem simStep.stepTimeBound_timed (bake : Bool) (p : Fin np) {h : ℕ} {M : GS P ω A}
    (hM : HistBound P A ω h M) {k : GS P ω A → ℕ × FProg.Timed Tx Hash np Sig} {T : ℕ}
    (hk : ∀ M', HistBound P A ω (h + (ℓ + 1)) M' → OracleAdv.Timed.StepTimeBound (k M') T) :
    OracleAdv.Timed.StepTimeBound (simStep.timed Sch P A cost i pk ω bake p M k)
      (T + stepCost cost h) := by
  let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec Sch false P ω A
  unfold simStep.timed
  split
  · refine (simCall.stepTimeBound_timed Sch A cost i pk ω hA _
      (t := cost.find + cost.step + T) fun r hr => ?_).mono ?_
    · split
      · exact ⟨by omega, trivial⟩
      · refine OracleAdv.Timed.stepTimeBound_delay (hk _ ⟨?_, ?_⟩)
        · unfold corruptStep
          cases bake <;> simpa [flood_msgs_adv_exec_order, fetch_msgs, rmv_zero_msgs] using hM.1
        · have h1 := outFilter_length_le Sch false (simPks i pk ω)
          have h3 := hM.2
          unfold corruptStep
          cases bake
          · have := h1 (fetch_msgs p M).2.t_now (fetch_msgs p M).2.history r.1
            simp only [fetch_msgs, rmv_zero_msgs] at this
            simp only [Bool.false_eq_true, if_false, flood_msgs_adv_history, List.length_append,
              List.length_map, fetch_msgs, rmv_zero_msgs]
            omega
          · have := h1 M.t_now M.history r.1
            simp only [if_true, flood_msgs_adv_history, List.length_append, List.length_map]
            omega
    · rw [stepCall_hist]
      have := Nat.mul_le_mul_right (1 + cost.sign) hM.2
      unfold stepCost
      omega
  · refine (OracleAdv.Timed.stepTimeBound_delay
      (hk _ (histBound_sStep Sch P A ω hA bake p hM))).mono ?_
    unfold stepCost
    omega

theorem simFold.stepTimeBound_timed (bake : Bool) {h : ℕ} {N : GS P ω A}
    (hN : HistBound P A ω h N) (l : List (Fin np))
    {k : GS P ω A → ℕ × FProg.Timed Tx Hash np Sig} {T : ℕ}
    (hk : ∀ M, HistBound P A ω (h + l.length * (ℓ + 1)) M →
      OracleAdv.Timed.StepTimeBound (k M) T) :
    OracleAdv.Timed.StepTimeBound (simFold.timed Sch P A cost i pk ω bake N l k)
      (T + l.length * stepCost cost (h + l.length * (ℓ + 1))) := by
  induction l generalizing k T with
  | nil => simpa [simFold.timed] using hk N (by simpa using hN)
  | cons p ps ih =>
    have e : (p :: ps).length * (ℓ + 1) = ps.length * (ℓ + 1) + (ℓ + 1) := by
      simp only [List.length_cons, Nat.succ_mul]
    have hmono := stepCost_mono cost
      (show h + ps.length * (ℓ + 1) ≤ h + (p :: ps).length * (ℓ + 1) by omega)
    refine (ih (T := T + stepCost cost (h + (p :: ps).length * (ℓ + 1))) fun M hM =>
      (simStep.stepTimeBound_timed Sch P A cost i pk ω hA bake p hM fun M' hM' =>
        hk M' (hM'.mono (by omega))).mono
          (show T + stepCost cost (h + ps.length * (ℓ + 1)) ≤
            T + stepCost cost (h + (p :: ps).length * (ℓ + 1)) by omega)).mono ?_
    have := Nat.mul_le_mul_left ps.length hmono
    simp only [List.length_cons, Nat.succ_mul] at this ⊢
    omega

theorem simPhase.stepTimeBound_timed {h : ℕ} {N : GS P ω A} (hN : HistBound P A ω h N)
    {k : GS P ω A → ℕ × FProg.Timed Tx Hash np Sig} {T : ℕ}
    (hk : ∀ M, HistBound P A ω (h + P.IP.length * (ℓ + 1)) M →
      OracleAdv.Timed.StepTimeBound (k M) T) :
    OracleAdv.Timed.StepTimeBound (simPhase.timed Sch P A cost i pk ω N k)
      (T + phaseCost cost P.IP.length (h + P.IP.length * (ℓ + 1))) := by
  let _ := ω.params P; let _ := ω.bparams P
  have hl : N.exec_order.length = P.IP.length := by rw [hN.1]
  unfold simPhase.timed phaseCost
  split
  · have := simFold.stepTimeBound_timed Sch P A cost i pk ω hA false hN N.exec_order
      (k := fun M => k { M with progress := .Delivered }) (T := T)
      (fun M hM => hk _ (by rw [hl] at hM; exact hM))
    rw [hl] at this
    exact (OracleAdv.Timed.stepTimeBound_delay this).mono (by omega)
  · have := simFold.stepTimeBound_timed Sch P A cost i pk ω hA true hN N.exec_order
      (k := fun M => k { M with progress := .Baked }) (T := T)
      (fun M hM => hk _ (by rw [hl] at hM; exact hM))
    rw [hl] at this
    exact (OracleAdv.Timed.stepTimeBound_delay this).mono (by omega)
  · refine OracleAdv.Timed.StepTimeBound.mono
      (OracleAdv.Timed.stepTimeBound_delay (hk _ ?_)) ?_
    · exact ⟨hN.1, hN.2.trans (Nat.le_add_right h (P.IP.length * (ℓ + 1)))⟩
    · omega

theorem simTrace.stepTimeBound_timed (j : ℕ)
    {k : GS P ω A → ℕ × FProg.Timed Tx Hash np Sig} {T : ℕ}
    (hk : ∀ M, HistBound P A ω (j * (P.IP.length * (ℓ + 1))) M →
      OracleAdv.Timed.StepTimeBound (k M) T) :
    OracleAdv.Timed.StepTimeBound (simTrace.timed Sch P A cost i pk ω j k)
      (T + j * phaseCost cost P.IP.length (j * (P.IP.length * (ℓ + 1)))) := by
  induction j generalizing k T with
  | zero => simpa [simTrace.timed] using hk _ (by simpa using histBound_sTrace_zero Sch P A ω false)
  | succ j ih =>
    have e : (j + 1) * (P.IP.length * (ℓ + 1)) =
        j * (P.IP.length * (ℓ + 1)) + P.IP.length * (ℓ + 1) := Nat.succ_mul _ _
    have hmono := phaseCost_mono cost P.IP.length
      (show j * (P.IP.length * (ℓ + 1)) ≤ (j + 1) * (P.IP.length * (ℓ + 1)) by omega)
    refine (ih (T := T + phaseCost cost P.IP.length ((j + 1) * (P.IP.length * (ℓ + 1))))
      fun M hM => ?_).mono ?_
    · have := simPhase.stepTimeBound_timed Sch P A cost i pk ω hA hM (k := k) (T := T)
        (fun M' hM' => hk M' (by rw [e]; exact hM'))
      rw [← e] at this
      exact this
    · have := Nat.mul_le_mul_left j hmono
      have e2 : (j + 1) * phaseCost cost P.IP.length ((j + 1) * (P.IP.length * (ℓ + 1))) =
          j * phaseCost cost P.IP.length ((j + 1) * (P.IP.length * (ℓ + 1))) +
            phaseCost cost P.IP.length ((j + 1) * (P.IP.length * (ℓ + 1))) := Nat.succ_mul _ _
      rw [e2]
      omega

theorem forgerProg.stepTimeBound_timed (K : ℕ) :
    OracleAdv.Timed.StepTimeBound (forgerProg.timed Sch P A cost i pk ω K)
      (1 + K * phaseCost cost P.IP.length (K * (P.IP.length * (ℓ + 1)))) :=
  simTrace.stepTimeBound_timed Sch P A cost i pk ω hA K fun _ _ =>
    ⟨Nat.zero_le _, le_refl 1, fun _ => ⟨Nat.zero_le _, trivial⟩⟩

end Forger

section ForgerTime

variable (Sch : PSigScheme (Block Tx Hash (Fin np)) PK SK Sig) [hS : Sch.Deterministic]
  (P : Protocol Tx Hash np n Hz) (A : Adversary Tx Hash np n Hz PK Sig) (cost : ReductionCost)

/-- **The costed forger.** The forger `forger Sch P A H cd μ W K i` with the step costs of
`cost`: the sample of the seed, then the costed simulation of `K` phases and the final
query. -/
noncomputable def forger.timed (H : HashScheme) (cd : H.Codec (BlockDom Tx Hash np Hz) Hash)
    (μ : PMF (Option (Fin np))) (W K : ℕ) (i : Fin np) (pk : PK) :
    FProg.Timed Tx Hash np Sig :=
  .rand (seedDist Sch H cd μ P.h0 W n) (fun ω => (forgerProg.timed Sch P A cost i pk ω K).1)
    fun ω => (forgerProg.timed Sch P A cost i pk ω K).2

/-- Erasing the step costs of the costed forger gives the forger. -/
theorem forger.erase_timed (H : HashScheme) (cd : H.Codec (BlockDom Tx Hash np Hz) Hash)
    (μ : PMF (Option (Fin np))) (W K : ℕ) (i : Fin np) (pk : PK) :
    (forger.timed Sch P A cost H cd μ W K i pk).erase = forger Sch P A H cd μ W K i pk := by
  simp only [forger.timed, forger, OracleAdv.Timed.erase, forgerProg.erase_timed]

/-- **Time of the forger.** For an adversary with at most `ℓ` output messages per call, the
forger runs in time at most `2 + K * phaseCost cost m (K * (m * (ℓ + 1)))` with
`m = P.IP.length`: per phase, the transition and at most `m` adversary calls, each with at
most one signing query or local signature per message of a history of at most
`K * (m * (ℓ + 1))` messages; one unit for the seed and one for the final query. -/
theorem forger.timeBound_timed {ℓ : ℕ} (hA : A.OutputBound ℓ) (H : HashScheme)
    (cd : H.Codec (BlockDom Tx Hash np Hz) Hash) (μ : PMF (Option (Fin np))) (W K : ℕ)
    (i : Fin np) (pk : PK) :
    (forger.timed Sch P A cost H cd μ W K i pk).TimeBound
      (2 + K * phaseCost cost P.IP.length (K * (P.IP.length * (ℓ + 1)))) := by
  refine ⟨by omega, fun ω => ?_⟩
  exact OracleAdv.Timed.StepTimeBound.mono
    (n := 2 + K * phaseCost cost P.IP.length (K * (P.IP.length * (ℓ + 1))) - 1)
    (forgerProg.stepTimeBound_timed Sch P A cost i pk ω hA K) (by omega)

end ForgerTime

/-! ## The costed collision finder -/

section Collision

variable (Sch : PSigScheme (Block Tx Hash (Fin np)) PK SK Sig) [hS : Sch.Deterministic]
  (P : Protocol Tx Hash np n Hz) (A : Adversary Tx Hash np n Hz PK Sig) (cost : ReductionCost)

/-- The work of the real execution of `K` phases for the seed `ω`: per adversary call, the
call and one signature per message of its history; per phase, the transition and `m`
party steps. -/
def execWork (ω : Seed Tx Hash np n Hz PK SK) (K : ℕ) : ℕ :=
  ((traceCalls Sch P ω A K).map fun c => cost.adv + c.hist.length * cost.sign).sum +
    K * (cost.phase + P.IP.length * cost.step)

/-- The number of blocks the collision finder searches: the genesis block and the broadcast
blocks of the state after `K` phases. -/
def collSearchLen (ω : Seed Tx Hash np n Hz PK SK) (K : ℕ) : ℕ :=
  letI := ω.params P; letI := ω.bparams P
  (block_hist_gb (sTrace Sch P ω A false K)).length

/-- **The costed collision finder.** Under the key `k`, the coins of `collCoins Sch P μ W`
are sampled; the output `collFind` is charged the real execution of `K` phases
(`execWork`) and the search over all pairs of the `collSearchLen` blocks at cost
`cost.pair` each. -/
noncomputable def collFinder.timed (H : HashScheme) (cd : H.Codec (BlockDom Tx Hash np Hz) Hash)
    (μ : PMF (Option (Fin np))) (W K : ℕ) (k : H.Key) :
    OracleAdv.Timed Empty Empty (H.Input × H.Input) :=
  .rand (collCoins Sch P μ W)
    (fun c =>
      execWork Sch P A cost (⟨c.1, cd.hashOn k, c.2⟩ : Seed Tx Hash np n Hz PK SK) K +
        collSearchLen Sch P A (⟨c.1, cd.hashOn k, c.2⟩ : Seed Tx Hash np n Hz PK SK) K *
          collSearchLen Sch P A (⟨c.1, cd.hashOn k, c.2⟩ : Seed Tx Hash np n Hz PK SK) K *
            cost.pair)
    fun c => .ret (collFind Sch P A H cd K k c)

/-- Erasing the step costs gives the coins and the output of `collFinder`. -/
theorem collFinder.erase_timed (H : HashScheme) (cd : H.Codec (BlockDom Tx Hash np Hz) Hash)
    (μ : PMF (Option (Fin np))) (W K : ℕ) (k : H.Key) :
    (collFinder.timed Sch P A cost H cd μ W K k).erase =
      .rand (collCoins Sch P μ W) fun c => .ret (collFind Sch P A H cd K k c) := rfl

/-- `collFinder` is the adversary that samples the coins of `collCoins` and outputs
`collFind`, the erased costed collision finder. -/
theorem collFinder_eq (H : HashScheme) (cd : H.Codec (BlockDom Tx Hash np Hz) Hash)
    (μ : PMF (Option (Fin np))) (W K : ℕ) :
    collFinder Sch P A H cd μ W K =
      CR_Search_Adversary.ofCoins (collCoins Sch P μ W) (collFind Sch P A H cd K) := rfl

/-- The output distribution of the erased costed collision finder is the image of the coins
under `collFind`, the distribution `CR_Search_Advantage_ofCoins` evaluates. -/
theorem collFinder.run_erase_timed (H : HashScheme) (cd : H.Codec (BlockDom Tx Hash np Hz) Hash)
    (μ : PMF (Option (Fin np))) (W K : ℕ) (k : H.Key) :
    (OracleAdv.run (fun (_ : Unit) (d : Empty) => d.elim)
        (collFinder.timed Sch P A cost H cd μ W K k).erase ()).map Prod.fst =
      (collCoins Sch P μ W).map (collFind Sch P A H cd K k) := by
  rw [collFinder.erase_timed, OracleAdv.run_rand, PMF.map_bind]
  simp only [OracleAdv.run_ret, PMF.pure_map]
  rfl

/-! ### Time of the collision finder -/

/-- The bound on the work of the real execution of `K` phases: at most `K * m` adversary
calls with histories of at most `K * (m * (ℓ + 1))` messages, and `K` phases of `m` party
steps. -/
def execBound (cost : ReductionCost) (m ℓ K : ℕ) : ℕ :=
  K * m * (cost.adv + K * (m * (ℓ + 1)) * cost.sign) + K * (cost.phase + m * cost.step)

variable {ℓ : ℕ} (hA : A.OutputBound ℓ)
include hA

theorem histBound_foldrCalls (ω : Seed Tx Hash np n Hz PK SK) (g : Fin np → GS P ω A → GS P ω A)
    (hg : ∀ p {h : ℕ} {M : GS P ω A}, HistBound P A ω h M → HistBound P A ω (h + (ℓ + 1)) (g p M))
    {h : ℕ} {N : GS P ω A} (hN : HistBound P A ω h N) (l : List (Fin np)) :
    ∀ x ∈ foldrCalls g N l, HistBound P A ω (h + l.length * (ℓ + 1)) x.2 := by
  induction l with
  | nil => simp [foldrCalls]
  | cons p ps ih =>
    intro x hx
    simp only [foldrCalls, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact (histBound_foldr P A ω hA g hg hN ps).mono (by simp only [List.length_cons]; nlinarith)
    · exact (ih x hx).mono (by simp only [List.length_cons]; nlinarith)

omit hA in
theorem length_foldrCalls {α β : Type*} (g : α → β → β) (N : β) (l : List α) :
    (foldrCalls g N l).length = l.length := by
  induction l with
  | nil => rfl
  | cons p ps ih => simp [foldrCalls, ih]

theorem phaseCalls_bound (ω : Seed Tx Hash np n Hz PK SK) {h : ℕ} {N : GS P ω A}
    (hN : HistBound P A ω h N) :
    (∀ c ∈ phaseCalls Sch P ω A N, c.hist.length ≤ h + P.IP.length * (ℓ + 1)) ∧
      (phaseCalls Sch P ω A N).length ≤ P.IP.length := by
  let _ := ω.params P; let _ := ω.bparams P
  have hl : N.exec_order.length = P.IP.length := by rw [hN.1]
  have key : ∀ (bake : Bool) (g : Fin np → GS P ω A → GS P ω A),
      (∀ p {h : ℕ} {M : GS P ω A}, HistBound P A ω h M →
        HistBound P A ω (h + (ℓ + 1)) (g p M)) →
      (∀ c ∈ (foldrCalls g N N.exec_order).flatMap (stepCalls P ω A bake),
        c.hist.length ≤ h + P.IP.length * (ℓ + 1)) ∧
      ((foldrCalls g N N.exec_order).flatMap (stepCalls P ω A bake)).length ≤
        P.IP.length := by
    intro bake g hg
    have hx := histBound_foldrCalls P A hA ω g hg hN N.exec_order
    rw [hl] at hx
    refine ⟨fun c hc => ?_, ?_⟩
    · obtain ⟨x, hxm, hc⟩ := List.mem_flatMap.1 hc
      have hb := (hx x hxm).2
      unfold stepCalls at hc
      split at hc
      · simp only [List.mem_singleton] at hc
        subst hc
        cases bake <;> exact hb
      · simp at hc
    · rw [List.length_flatMap]
      calc ((foldrCalls g N N.exec_order).map fun x => (stepCalls P ω A bake x).length).sum
          ≤ ((foldrCalls g N N.exec_order).map fun _ => 1).sum := by
            refine List.sum_le_sum fun x _ => ?_
            unfold stepCalls
            split <;> simp
        _ = P.IP.length := by simpa [hl] using length_foldrCalls g N N.exec_order
  unfold phaseCalls
  split
  · exact key false _ fun p _ _ hM => histBound_sRcv Sch P A ω hA false p hM
  · exact key true _ fun p _ _ hM => histBound_sBake Sch P A ω hA false p hM
  · simp

theorem traceCalls_bound (ω : Seed Tx Hash np n Hz PK SK) (K : ℕ) :
    (∀ c ∈ traceCalls Sch P ω A K, c.hist.length ≤ K * (P.IP.length * (ℓ + 1))) ∧
      (traceCalls Sch P ω A K).length ≤ K * P.IP.length := by
  induction K with
  | zero => simp [traceCalls]
  | succ K ih =>
    have hp := phaseCalls_bound Sch P A hA ω (histBound_sTrace Sch P A ω hA K)
    rw [traceCalls_succ]
    refine ⟨fun c hc => ?_, ?_⟩
    · rcases List.mem_append.1 hc with hc | hc
      · exact (ih.1 c hc).trans (Nat.mul_le_mul_right _ (Nat.le_succ K))
      · exact (hp.1 c hc).trans (by rw [Nat.succ_mul])
    · rw [List.length_append, Nat.succ_mul]
      have := ih.2
      have := hp.2
      omega

theorem execWork_le (ω : Seed Tx Hash np n Hz PK SK) (K : ℕ) :
    execWork Sch P A cost ω K ≤ execBound cost P.IP.length ℓ K := by
  have hb := traceCalls_bound Sch P A hA ω K
  unfold execWork execBound
  have hs : ((traceCalls Sch P ω A K).map fun c => cost.adv + c.hist.length * cost.sign).sum ≤
      (traceCalls Sch P ω A K).length *
        (cost.adv + K * (P.IP.length * (ℓ + 1)) * cost.sign) := by
    have := List.sum_le_card_nsmul ((traceCalls Sch P ω A K).map fun c =>
      cost.adv + c.hist.length * cost.sign) (cost.adv + K * (P.IP.length * (ℓ + 1)) * cost.sign)
      (by
        intro x hx
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
        have := Nat.mul_le_mul_right cost.sign (hb.1 c hc)
        omega)
    simpa using this
  have := Nat.mul_le_mul_right (cost.adv + K * (P.IP.length * (ℓ + 1)) * cost.sign) hb.2
  omega

theorem collSearchLen_le (ω : Seed Tx Hash np n Hz PK SK) (K : ℕ) :
    collSearchLen Sch P A ω K ≤ 1 + K * (P.IP.length * (ℓ + 1)) := by
  let _ := ω.params P; let _ := ω.bparams P
  have := (histBound_sTrace Sch P A ω hA K).2
  simp only [collSearchLen, block_hist_gb, block_history, List.length_cons, List.length_map]
  omega

/-- **Time of the collision finder.** For an adversary with at most `ℓ` output messages per
call, under every key the collision finder runs in time at most
`1 + execBound cost m ℓ K + B * B * cost.pair` with `m = P.IP.length` and
`B = 1 + K * (m * (ℓ + 1))`: the sample of the coins, the real execution of `K` phases and
the search over all pairs of at most `B` blocks. -/
theorem collFinder.timeBound_timed (H : HashScheme) (cd : H.Codec (BlockDom Tx Hash np Hz) Hash)
    (μ : PMF (Option (Fin np))) (W K : ℕ) (k : H.Key) :
    (collFinder.timed Sch P A cost H cd μ W K k).TimeBound
      (1 + (execBound cost P.IP.length ℓ K +
        (1 + K * (P.IP.length * (ℓ + 1))) * (1 + K * (P.IP.length * (ℓ + 1))) * cost.pair)) := by
  refine ⟨by omega, fun c => ⟨?_, trivial⟩⟩
  have h1 := execWork_le Sch P A cost hA (⟨c.1, cd.hashOn k, c.2⟩ : Seed Tx Hash np n Hz PK SK) K
  have h2 := collSearchLen_le Sch P A hA (⟨c.1, cd.hashOn k, c.2⟩ : Seed Tx Hash np n Hz PK SK) K
  have h3 := Nat.mul_le_mul_right cost.pair (Nat.mul_le_mul h2 h2)
  simp only [Nat.add_sub_cancel_left]
  omega

end Collision

end CatCryptCore.Consensus.PoSNSB
