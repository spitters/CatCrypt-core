/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.X3DHSquare
public import CatCryptCore.Crypto.UCSimulatorCostGraded
public import CatCryptCore.Crypto.UCSimulatorTimed
import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic
public import CatCryptCore.Tactics.DeriveSimulator
import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.DeriveTimeBound.Basic

/-!
# Running time of the X3DH simulator

`derive_reduction` builds the costed form `simProt.timed` of the multi-call simulator `simProt`
of `X3DHSquare.lean` and its erasure theorem. The start step `simStart` is read as a computation
tree: each draw of a long-term pair, of a session secret and of a key-derivation value is a
`sample` node, and the record updates, the derivation inputs `aliceInp` and `bobInp`, the group
operations and the decisions are priced by the cost model of `derive_timed`. A lookup in the
key-derivation table costs in the length of the table.

The key-derivation table and the list of notices grow by at most one entry per activation, and
every other table of the state starts each step at the zero cost companion. The invariant
`SimInv i` bounds the two lengths by `i` after `i` activations, so that a step costs at most
`a + 40 i` (`simProt.timeBoundGraded_timed`), the graded form for a simulator whose state grows
with the activations, and `derive_simulator` lifts it to `x3dhSim`.

Only `PQXDHSquareTimed.lean` imports this file.

## Main results

* `simProt.timed`, `simProt.erase_timed`: the costed multi-call simulator and its erasure.
* `simProt.start.tree.timeBound_timed`: the time of `start`, linear in the time of the group
  operations, the length of the key-derivation table and the number of notices.
* `simProt.timeBoundGraded_timed`: its graded time bound on the invariant `SimInv`.
* `x3dhSim.timed`, `x3dhSim.erase_timed`, `x3dhSim.timeBoundGraded_timed`: the costed bundled
  simulator, its erasure, and its graded time bound.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.X3DHSquare

open CatCrypt.Core

set_option maxHeartbeats 400000 in
-- The start step reflects ten event cases with nested record updates.
derive_reduction simProt

derive_time_bound simProt.resume.tree
derive_time_bound simProt.finish.tree

section Time

open SPTree.Timed (stepTime_bind_bind_le stepTime_pair stepTime_delay_bind_const_le
  stepTime_cost_le)

variable {S W K : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K] [Nonempty K]
  [Inhabited K]

-- The costed steps of `simProt` are compiled through the auxiliary matchers of its source, and
-- the bounds below unfold them by name.
set_option linter.auxLemma false

/-- The costed copy of the real state: the session records, corrupt parties, long-term secrets
and session secrets with their cost companions, the notices, the cursor and the table of the
key derivation. -/
abbrev RHat (S W K : Type) : Type :=
  (((UCTransparent.FAKE.Inst → Option (UCTransparent.FAKE.Rec K)) ×
      (UCTransparent.FAKE.Inst → ℕ)) ×
    ((UCTransparent.FAKE.PartyId → Bool) × (UCTransparent.FAKE.PartyId → ℕ)) ×
      List UCTransparent.FAKE.Notice × ℕ) ×
  ((UCTransparent.FAKE.PartyId → Option (S × S)) × (UCTransparent.FAKE.PartyId → ℕ)) ×
    ((UCTransparent.FAKE.Inst → Option S) × (UCTransparent.FAKE.Inst → ℕ)) × List (Inp W × K)

/-- The costed state of the simulator: the costed copy of the real state, the table of inputs
with its cost companion, and the phase. -/
abbrev SimHat (S W K : Type) : Type :=
  RHat S W K × ((UCTransparent.FAKE.Inst → Option (Inp W)) × (UCTransparent.FAKE.Inst → ℕ)) ×
    Phase S W K

omit [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The first lookup of long-term secrets in `complete` and `send` (`ltStep` on the input
state) costs at most `3 + T` when the cost companion of the secrets is at most `T`. -/
theorem lt1_time (s : SimHat S W K) (sid : UCTransparent.FAKE.SessionId)
    (pid : UCTransparent.FAKE.PartyId) {T : ℕ} (hc : ∀ p, s.1.2.1.2 p ≤ T) :
    SPTree.Timed.stepTime (simProt.start.tree.match_3.timed s sid pid s.1.2.1.2) ≤ 3 + T := by
  have := hc pid
  simp only [simProt.start.tree.match_3.timed, SPTree.Timed.stepTime]
  split <;> simp only [SPTree.Timed.time_ret, SPTree.Timed.time_sample] <;>
    grind [Finset.sup_eq_bot_iff, Nat.bot_eq_zero]

omit [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The first lookup of long-term secrets keeps the notices, the key-derivation table and the
cost companion of the corrupt parties, and raises the cost companion of the secrets by at most
three. -/
theorem lt1_allRet (s : SimHat S W K) (sid : UCTransparent.FAKE.SessionId)
    (pid : UCTransparent.FAKE.PartyId) {T : ℕ} (hc : ∀ p, s.1.2.1.2 p ≤ T) :
    SPTree.Timed.AllRet (fun y => y.2.2.2.2 = s.1.2.2.2 ∧ y.2.1.2.2.1 = s.1.1.2.2.1 ∧
        (∀ p, y.2.2.1.2 p ≤ T + 3) ∧ y.2.1.2.1.2 = s.1.1.2.1.2)
      (simProt.start.tree.match_3.timed s sid pid s.1.2.1.2).2 := by
  simp only [simProt.start.tree.match_3.timed]
  split
  · exact ⟨rfl, rfl, fun p => by have := hc p; grind, rfl⟩
  · intro b
    refine ⟨rfl, rfl, fun p => ?_, rfl⟩
    have := hc p
    dsimp only
    split <;> omega

omit [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The second lookup of long-term secrets (`ltStep` at the peer) costs at most `3 + T` when
the cost companion of the secrets is at most `T`. -/
theorem lt2_time (r : UCTransparent.FAKE.Rec K) (x : (S × S) × RSt S W K) (h : RHat S W K)
    {T : ℕ} (hc : ∀ p, h.2.1.2 p ≤ T) :
    SPTree.Timed.stepTime (simProt.start.tree.match_4.timed r x h) ≤ 3 + T := by
  have := hc r.peer
  simp only [simProt.start.tree.match_4.timed, SPTree.Timed.stepTime, SPTree.Timed.delay]
  split <;> simp only [SPTree.Timed.time_ret, SPTree.Timed.time_sample] <;>
    grind [Finset.sup_eq_bot_iff, Nat.bot_eq_zero]

omit [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The second lookup of long-term secrets keeps the notices and the key-derivation table, and
takes the cost companion of the corrupt parties from the costed state `h`. -/
theorem lt2_allRet (r : UCTransparent.FAKE.Rec K) (x : (S × S) × RSt S W K) (h : RHat S W K) :
    SPTree.Timed.AllRet (fun y => y.2.2.2.2 = x.2.ro ∧ y.2.1.2.2.1 = x.2.st.notices ∧
        y.2.1.2.1.2 = h.1.2.1.2)
      (simProt.start.tree.match_4.timed r x h).2 := by
  simp only [simProt.start.tree.match_4.timed, SPTree.Timed.delay]
  split
  · exact ⟨rfl, rfl, rfl⟩
  · exact fun _ => ⟨rfl, rfl, rfl⟩

omit [Fintype S] [Inhabited K] in
/-- The key derivation at the input of the initiator in `complete` costs at most
`12 + 3 t_toFun + 4 t_exp + 5 L` on a table of length `L`. -/
theorem kdfIni_time (G : PAKE.DHExtract.DHGroup S W) (sid : UCTransparent.FAKE.SessionId)
    (pid : UCTransparent.FAKE.PartyId) (r : UCTransparent.FAKE.Rec K) (ek opk : S)
    (x y : (S × S) × RSt S W K) (toFunCost : S → ℕ) (expCost : W → S → ℕ) {te tf : ℕ}
    (he : ∀ a b, expCost a b ≤ te) (hf : ∀ a, toFunCost a ≤ tf) :
    SPTree.Timed.stepTime
        (simProt.start.tree.match_5.timed G sid pid r ek opk x y toFunCost expCost) ≤
      12 + 3 * tf + 4 * te + 5 * y.2.ro.length := by
  have hl := fun a => List.lookup.timedCost_le a y.2.ro
  simp only [simProt.start.tree.match_5.timed, SPTree.Timed.stepTime]
  split <;> simp only [SPTree.Timed.time_ret, SPTree.Timed.time_sample] <;>
    grind [Finset.sup_eq_bot_iff, Nat.bot_eq_zero]

omit [Fintype S] [Inhabited K] in
/-- The key derivation at the input of the initiator adds at most one entry to the table. -/
theorem kdfIni_allRet (G : PAKE.DHExtract.DHGroup S W) (sid : UCTransparent.FAKE.SessionId)
    (pid : UCTransparent.FAKE.PartyId) (r : UCTransparent.FAKE.Rec K) (ek opk : S)
    (x y : (S × S) × RSt S W K) (toFunCost : S → ℕ) (expCost : W → S → ℕ) :
    SPTree.Timed.AllRet (fun z => z.2.length ≤ y.2.ro.length + 1)
      (simProt.start.tree.match_5.timed G sid pid r ek opk x y toFunCost expCost).2 := by
  simp only [simProt.start.tree.match_5.timed]
  split
  · exact Nat.le_succ _
  · exact fun _ => le_rfl

/-- The `complete` step of the costed simulator (`simComplete`), from a costed state whose cost
companions of the long-term secrets, of the inputs and of the corrupt parties vanish, costs at
most `60 + 3 t_coe + 3 t_toFun + 8 t_exp + 5 L` on a key-derivation table of length `L`. The
test `Exposed` reads the corrupt parties at their cost companion. -/
theorem complete_time (G : PAKE.DHExtract.DHGroup S W) (x : SimHat S W K)
    (coe : S ≃ W → S → W) (coeCost : S ≃ W → S → ℕ) (sid : UCTransparent.FAKE.SessionId)
    (pid : UCTransparent.FAKE.PartyId) (expCost : W → S → ℕ) (toFunCost : S → ℕ)
    (hlt : x.1.2.1.2 = fun _ => 0) (hinp : x.2.1.2 = fun _ => 0)
    (hcor : x.1.1.2.1.2 = fun _ => 0) {tc te tf : ℕ}
    (hc : ∀ a b, coeCost a b ≤ tc) (he : ∀ a b, expCost a b ≤ te)
    (hf : ∀ a, toFunCost a ≤ tf) :
    SPTree.Timed.stepTime (simProt.start.tree.match_7.timed G x coe coeCost sid pid
        (fun _ => 0) (fun _ => 0) expCost toFunCost) ≤
      60 + 3 * tc + 3 * tf + 8 * te + 5 * x.1.2.2.2.length := by
  simp only [simProt.start.tree.match_7.timed]
  split
  · rename_i _ _ r ek _ _
    simp only [simProt.start.tree.match_6.timed]
    rw [stepTime_pair, SPTree.Timed.stepTime_delay, stepTime_pair]
    rcases hO : opkOf (⟨⟨x.1.1.1.1, x.1.1.2.1.1, x.1.1.2.2.1, x.1.1.2.2.2⟩, x.1.2.1.1,
        x.1.2.2.1.1, x.1.2.2.2⟩ : RSt S W K) sid r.peer with _ | opk
    · simp only [SPTree.Timed.stepTime, SPTree.Timed.time_ret]
      split <;> (try split_ifs) <;> omega
    · simp only [SPTree.Timed.stepTime_delay]
      split_ifs
      · refine le_trans (Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_left
          (Nat.add_le_add_left (stepTime_bind_bind_le 1 1 _ _ _
            (lt1_time x sid pid (T := 0) fun p => by simp [hlt])
            (lt1_allRet x sid pid (T := 0) fun p => by simp [hlt])
            (fun a ha => lt2_time r _ a.2 (T := 0 + 3) ha.2.2.1)
            (fun a _ => lt2_allRet r _ a.2)
            (TF := 7 + 3 * tc + 4 * te + 4 + (15 + 3 * tf + 4 * te + 5 * x.1.2.2.2.length))
            ?_) 3) _) 1) _) ?_
        · intro a b ha hb
          have hE : b.2.1.2.1.2 = fun _ => 0 := hb.2.2.trans (ha.2.2.2.trans hcor)
          have key : ∀ {γ : Type} (C E : ℕ) (D : ℕ × SPTree.Timed γ) {TC TD : ℕ}, C ≤ TC →
              SPTree.Timed.stepTime D ≤ TD →
                SPTree.Timed.stepTime (C + (E + D.1), D.2) ≤ TC + E + TD :=
            fun C E D hC hD => by simp only [SPTree.Timed.stepTime] at hD ⊢; omega
          refine le_trans (key _ _ _ (TC := 7 + 3 * tc + 4 * te)
            (TD := 15 + 3 * tf + 4 * te + 5 * x.1.2.2.2.length) ?_ ?_) ?_
          · grind
          · split_ifs
            · refine le_trans (stepTime_delay_bind_const_le 1 2 _ _
                (kdfIni_time G sid pid r ek opk _ _ toFunCost expCost he hf)) ?_
              dsimp only at hb ⊢
              rw [hb.1, ha.1]
              omega
            all_goals
              simp only [SPTree.Timed.stepTime, SPTree.Timed.time_ret, hinp]
              split <;> omega
          · simp only [hE]
            omega
        · split <;> (try split_ifs) <;> omega
      · simp only [SPTree.Timed.stepTime, SPTree.Timed.time_ret]
        split <;> (try split_ifs) <;> omega
  · simp only [SPTree.Timed.stepTime, SPTree.Timed.time_ret]
    omega

omit [Fintype S] [Inhabited K] in
/-- The key derivation at the input of the responder in `send` costs at most
`12 + 3 t_toFun + 4 t_exp + 5 L` on a table of length `L`. -/
theorem kdfRes_time (G : PAKE.DHExtract.DHGroup S W) (sid : UCTransparent.FAKE.SessionId)
    (pid : UCTransparent.FAKE.PartyId) (e : W) (r : UCTransparent.FAKE.Rec K) (opk : S)
    (x y : (S × S) × RSt S W K) (toFunCost : S → ℕ) (expCost : W → S → ℕ) {te tf : ℕ}
    (he : ∀ a b, expCost a b ≤ te) (hf : ∀ a, toFunCost a ≤ tf) :
    SPTree.Timed.stepTime
        (simProt.start.tree.match_10.timed G sid pid e r opk x y toFunCost expCost) ≤
      12 + 3 * tf + 4 * te + 5 * y.2.ro.length := by
  have hl := fun a => List.lookup.timedCost_le a y.2.ro
  simp only [simProt.start.tree.match_10.timed, SPTree.Timed.stepTime]
  split <;> simp only [SPTree.Timed.time_ret, SPTree.Timed.time_sample] <;>
    grind [Finset.sup_eq_bot_iff, Nat.bot_eq_zero]

omit [Fintype S] [Inhabited K] in
/-- The key derivation at the input of the responder adds at most one entry to the table. -/
theorem kdfRes_allRet (G : PAKE.DHExtract.DHGroup S W) (sid : UCTransparent.FAKE.SessionId)
    (pid : UCTransparent.FAKE.PartyId) (e : W) (r : UCTransparent.FAKE.Rec K) (opk : S)
    (x y : (S × S) × RSt S W K) (toFunCost : S → ℕ) (expCost : W → S → ℕ) :
    SPTree.Timed.AllRet (fun z => z.2.length ≤ y.2.ro.length + 1)
      (simProt.start.tree.match_10.timed G sid pid e r opk x y toFunCost expCost).2 := by
  simp only [simProt.start.tree.match_10.timed]
  split
  · exact Nat.le_succ _
  · exact fun _ => le_rfl

/-- The `send` step of the costed simulator (`simSend`), from a costed state whose cost
companions of the long-term secrets, of the inputs and of the corrupt parties vanish, costs at
most `60 + 3 t_coe + 3 t_toFun + 8 t_exp + 5 L` on a key-derivation table of length `L`. The
test `Exposed` reads the corrupt parties at their cost companion. -/
theorem send_time (G : PAKE.DHExtract.DHGroup S W) (x : SimHat S W K)
    (coe : S ≃ W → S → W) (coeCost : S ≃ W → S → ℕ) (sid : UCTransparent.FAKE.SessionId)
    (pid : UCTransparent.FAKE.PartyId) (e : W) (expCost : W → S → ℕ) (toFunCost : S → ℕ)
    (hlt : x.1.2.1.2 = fun _ => 0) (hinp : x.2.1.2 = fun _ => 0)
    (hcor : x.1.1.2.1.2 = fun _ => 0) {tc te tf : ℕ}
    (hc : ∀ a b, coeCost a b ≤ tc) (he : ∀ a b, expCost a b ≤ te)
    (hf : ∀ a, toFunCost a ≤ tf) :
    SPTree.Timed.stepTime (simProt.start.tree.match_11.timed G x coe coeCost sid pid e expCost
        (fun _ => 0) (fun _ => 0) toFunCost) ≤
      60 + 3 * tc + 3 * tf + 8 * te + 5 * x.1.2.2.2.length := by
  simp only [simProt.start.tree.match_11.timed,
    show @simProt.start.tree.match_8.timed S W K _ _ = @simProt.start.tree.match_3.timed S W K _ _
      from rfl,
    show @simProt.start.tree.match_9.timed S W K _ _ = @simProt.start.tree.match_4.timed S W K _ _
      from rfl]
  rw [stepTime_pair]
  split
  · rename_i _ _ r opk _ _
    rw [SPTree.Timed.stepTime_delay]
    split_ifs
    · refine le_trans (Nat.add_le_add_left (Nat.add_le_add_left
        (stepTime_bind_bind_le 1 1 _ _ _
          (lt1_time x sid pid (T := 0) fun p => by simp [hlt])
          (lt1_allRet x sid pid (T := 0) fun p => by simp [hlt])
          (fun a ha => lt2_time r _ a.2 (T := 0 + 3) ha.2.2.1)
          (fun a _ => lt2_allRet r _ a.2)
          (TF := 7 + 3 * tc + 4 * te + 4 + (15 + 3 * tf + 4 * te + 5 * x.1.2.2.2.length))
          ?_) 3) _) ?_
      · intro a b ha hb
        have hE : b.2.1.2.1.2 = fun _ => 0 := hb.2.2.trans (ha.2.2.2.trans hcor)
        have key : ∀ {γ : Type} (C E : ℕ) (D : ℕ × SPTree.Timed γ) {TC TD : ℕ}, C ≤ TC →
            SPTree.Timed.stepTime D ≤ TD →
              SPTree.Timed.stepTime (C + (E + D.1), D.2) ≤ TC + E + TD :=
          fun C E D hC hD => by simp only [SPTree.Timed.stepTime] at hD ⊢; omega
        refine le_trans (key _ _ _ (TC := 7 + 3 * tc + 4 * te)
          (TD := 15 + 3 * tf + 4 * te + 5 * x.1.2.2.2.length) ?_ ?_) ?_
        · grind
        · split_ifs
          · refine le_trans (stepTime_delay_bind_const_le 1 2 _ _
              (kdfRes_time G sid pid e r opk _ _ toFunCost expCost he hf)) ?_
            dsimp only at hb ⊢
            rw [hb.1, ha.1]
            omega
          all_goals
            simp only [SPTree.Timed.stepTime, SPTree.Timed.time_ret, hinp]
            split <;> omega
        · simp only [hE]
          omega
      · omega
    · simp only [SPTree.Timed.stepTime, SPTree.Timed.time_ret]
      omega
  · simp only [SPTree.Timed.stepTime, SPTree.Timed.time_ret]
    omega

/-- The bound of the `complete` step on the costed tree of `start`. -/
theorem start_complete_time (G : PAKE.DHExtract.DHGroup S W) (coe : S ≃ W → S → W)
    (coeCost : S ≃ W → S → ℕ) (expCost : W → S → ℕ) (toFunCost : S → ℕ) (s : SimSt S W K)
    (sid : UCTransparent.FAKE.SessionId) (pid : UCTransparent.FAKE.PartyId) {tc te tf : ℕ}
    (hc : ∀ a b, coeCost a b ≤ tc) (he : ∀ a b, expCost a b ≤ te)
    (hf : ∀ a, toFunCost a ≤ tf) :
    SPTree.Timed.stepTime (simProt.start.tree.timed G coe coeCost s (.inr (.complete sid pid))
        expCost toFunCost) ≤
      63 + 3 * tc + 3 * tf + 8 * te + 5 * s.1.ro.length := by
  simp only [simProt.start.tree.timed]
  rw [SPTree.Timed.stepTime_delay]
  refine le_trans (SPTree.Timed.bind_ret_stepTime_le _ _) ?_
  simp only [SPTree.Timed.stepTime_delay, simProt.start.tree.match_13.timed]
  rw [stepTime_pair]
  refine le_trans (Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_left
    (complete_time G _ coe coeCost sid pid expCost toFunCost (by rfl) (by rfl) (by rfl) hc he
      hf) _)
    _) _) ?_
  dsimp only
  omega

/-- The bound of the `send` step on the costed tree of `start`. -/
theorem start_send_time (G : PAKE.DHExtract.DHGroup S W) (coe : S ≃ W → S → W)
    (coeCost : S ≃ W → S → ℕ) (expCost : W → S → ℕ) (toFunCost : S → ℕ) (s : SimSt S W K)
    (sid : UCTransparent.FAKE.SessionId) (pid : UCTransparent.FAKE.PartyId) (e : W)
    {tc te tf : ℕ} (hc : ∀ a b, coeCost a b ≤ tc) (he : ∀ a b, expCost a b ≤ te)
    (hf : ∀ a, toFunCost a ≤ tf) :
    SPTree.Timed.stepTime (simProt.start.tree.timed G coe coeCost s (.inr (.send sid pid e))
        expCost toFunCost) ≤
      63 + 3 * tc + 3 * tf + 8 * te + 5 * s.1.ro.length := by
  simp only [simProt.start.tree.timed]
  rw [SPTree.Timed.stepTime_delay]
  refine le_trans (SPTree.Timed.bind_ret_stepTime_le _ _) ?_
  simp only [SPTree.Timed.stepTime_delay, simProt.start.tree.match_13.timed]
  rw [stepTime_pair]
  refine le_trans (Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_left
    (send_time G _ coe coeCost sid pid e expCost toFunCost (by rfl) (by rfl) (by rfl) hc he
      hf) _)
    _) _) ?_
  dsimp only
  omega

/-- The invariant of the costed state after `i` activations: the table of the key derivation
and the list of notices have at most `i` entries. -/
def HatInv (i : ℕ) (y : SimHat S W K) : Prop :=
  y.1.2.2.2.length ≤ i ∧ y.1.1.2.2.1.length ≤ i

/-- The invariant of the state of the simulator after `i` activations: the table of the key
derivation and the list of notices have at most `i` entries. -/
def SimInv (i : ℕ) (s : SimSt S W K) : Prop :=
  s.1.ro.length ≤ i ∧ s.1.st.notices.length ≤ i

omit [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The lookup of long-term secrets at `pub` keeps the notices and the key-derivation table. -/
theorem simProt_lt0_allRet (s : SimHat S W K) (pid : UCTransparent.FAKE.PartyId) :
    SPTree.Timed.AllRet (fun y => y.2.2.2.2 = s.1.2.2.2 ∧ y.2.1.2.2.1 = s.1.1.2.2.1)
      (simProt.start.tree.match_1.timed s pid s.1.2.1.2).2 := by
  simp only [simProt.start.tree.match_1.timed]
  split
  · exact ⟨rfl, rfl⟩
  · exact fun _ => ⟨rfl, rfl⟩

omit [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The lookup of long-term secrets at `corrupt` keeps the notices and the key-derivation
table. -/
theorem simProt_lt0_allRet' (s : SimHat S W K) (pid : UCTransparent.FAKE.PartyId) :
    SPTree.Timed.AllRet (fun y => y.2.2.2.2 = s.1.2.2.2 ∧ y.2.1.2.2.1 = s.1.1.2.2.1)
      (simProt.start.tree.match_2.timed s pid s.1.2.1.2).2 := by
  simp only [simProt.start.tree.match_2.timed]
  split
  · exact ⟨rfl, rfl⟩
  · exact fun _ => ⟨rfl, rfl⟩

omit [Field S] [Fintype S] [Inhabited K] in
/-- A query of the key derivation adds at most one entry to the table. -/
theorem simProt_kdf_allRet (s : SimHat S W K) (x : Inp W) :
    SPTree.Timed.AllRet (fun z => z.2.length ≤ s.1.2.2.2.length + 1)
      (simProt.start.tree.match_12.timed s x).2 := by
  simp only [simProt.start.tree.match_12.timed]
  split
  · exact Nat.le_succ _
  · exact fun _ => le_rfl

/-- The `complete` step preserves the invariant, one activation later. -/
theorem complete_allRet (G : PAKE.DHExtract.DHGroup S W) (x : SimHat S W K)
    (coe : S ≃ W → S → W) (coeCost : S ≃ W → S → ℕ) (sid : UCTransparent.FAKE.SessionId)
    (pid : UCTransparent.FAKE.PartyId) (rc ec : UCTransparent.FAKE.Inst → ℕ)
    (expCost : W → S → ℕ) (toFunCost : S → ℕ) (hlt : x.1.2.1.2 = fun _ => 0) {i : ℕ}
    (hx : HatInv i x) :
    SPTree.Timed.AllRet (fun y => HatInv (i + 1) y.1)
      (simProt.start.tree.match_7.timed G x coe coeCost sid pid rc ec expCost toFunCost).2 := by
  obtain ⟨hro, hn⟩ := hx
  have hs : HatInv (i + 1) x := ⟨by omega, by omega⟩
  simp only [simProt.start.tree.match_7.timed]
  split
  · rename_i _ _ r ek _ _
    simp only [simProt.start.tree.match_6.timed, SPTree.Timed.delay]
    split
    · split_ifs
      · refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_mono (fun a ha => ?_) _
          (lt1_allRet x sid pid (T := 0) fun p => by simp [hlt]))
        refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_mono (fun b hb => ?_) _
          (lt2_allRet r _ a.2))
        dsimp only at hb
        split_ifs
        · refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_mono (fun z hz => ?_) _
            (kdfIni_allRet G sid pid r ek _ _ _ toFunCost expCost))
          dsimp only at hz
          exact ⟨by dsimp only; grind, by dsimp only; grind⟩
        all_goals exact ⟨by dsimp only; grind, by dsimp only; grind⟩
      · exact hs
    · exact hs
  · exact hs

/-- The `send` step preserves the invariant, one activation later. -/
theorem send_allRet (G : PAKE.DHExtract.DHGroup S W) (x : SimHat S W K)
    (coe : S ≃ W → S → W) (coeCost : S ≃ W → S → ℕ) (sid : UCTransparent.FAKE.SessionId)
    (pid : UCTransparent.FAKE.PartyId) (e : W) (rc ec : UCTransparent.FAKE.Inst → ℕ)
    (expCost : W → S → ℕ) (toFunCost : S → ℕ) (hlt : x.1.2.1.2 = fun _ => 0) {i : ℕ}
    (hx : HatInv i x) :
    SPTree.Timed.AllRet (fun y => HatInv (i + 1) y.1)
      (simProt.start.tree.match_11.timed G x coe coeCost sid pid e expCost rc ec toFunCost).2 := by
  obtain ⟨hro, hn⟩ := hx
  have hs : HatInv (i + 1) x := ⟨by omega, by omega⟩
  simp only [simProt.start.tree.match_11.timed, SPTree.Timed.delay,
    show @simProt.start.tree.match_8.timed S W K _ _ = @simProt.start.tree.match_3.timed S W K _ _
      from rfl,
    show @simProt.start.tree.match_9.timed S W K _ _ = @simProt.start.tree.match_4.timed S W K _ _
      from rfl]
  split
  · rename_i _ _ r opk _ _
    split_ifs
    · refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_mono (fun a ha => ?_) _
        (lt1_allRet x sid pid (T := 0) fun p => by simp [hlt]))
      refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_mono (fun b hb => ?_) _
        (lt2_allRet r _ a.2))
      dsimp only at hb
      split_ifs
      · refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_mono (fun z hz => ?_) _
          (kdfRes_allRet G sid pid e r opk _ _ toFunCost expCost))
        dsimp only at hz
        exact ⟨by dsimp only; grind, by dsimp only; grind⟩
      all_goals exact ⟨by dsimp only; grind, by dsimp only; grind⟩
    · exact hs
  · exact hs

/-- The `start` step preserves the invariant, one activation later. -/
theorem simProt.start_allRet (G : PAKE.DHExtract.DHGroup S W) (coe : S ≃ W → S → W)
    (coeCost : S ≃ W → S → ℕ) (expCost : W → S → ℕ) (toFunCost : S → ℕ) (s : SimSt S W K)
    (e : OEv W) {i : ℕ} (hs : SimInv i s) :
    SPTree.Timed.AllRet (fun y => SimInv (i + 1) y.1)
      (simProt.start.tree.timed G coe coeCost s e expCost toFunCost).2 := by
  obtain ⟨hro, hn⟩ := hs
  simp only [simProt.start.tree.timed, SPTree.Timed.delay]
  refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_mono
    (Q := fun y : SimHat S W K × Dec S W K => HatInv (i + 1) y.1) (fun y hy => hy) _ ?_)
  simp only [simProt.start.tree.match_13.timed, SPTree.Timed.delay]
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ | pid |
    ⟨sid, pid⟩ | ⟨sid, pid, e⟩ | x)
  · dsimp only
    split_ifs
    · exact fun _ => ⟨by dsimp only; omega, by dsimp only; omega⟩
    · exact fun _ => ⟨by dsimp only; omega, by
        dsimp only
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega⟩
    · exact ⟨by dsimp only; omega, by dsimp only; omega⟩
  · exact ⟨by dsimp only; omega, by dsimp only; omega⟩
  · exact ⟨by dsimp only; omega, by dsimp only; omega⟩
  · refine ⟨by dsimp only; omega, ?_⟩
    dsimp only
    split <;> dsimp only <;> omega
  · dsimp only
    refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_mono (fun a ha => ?_) _
      (simProt_lt0_allRet _ pid))
    exact ⟨by dsimp only; grind, by dsimp only; grind⟩
  · exact ⟨by dsimp only; omega, by dsimp only; omega⟩
  · dsimp only
    split_ifs
    · exact ⟨by dsimp only; omega, by dsimp only; omega⟩
    · refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_mono (fun a ha => ?_) _
        (simProt_lt0_allRet' _ pid))
      exact ⟨by dsimp only; grind, by dsimp only; grind⟩
  · exact complete_allRet G _ coe coeCost sid pid _ _ expCost toFunCost (by rfl)
      ⟨by dsimp only; omega, by dsimp only; omega⟩
  · exact send_allRet G _ coe coeCost sid pid e (fun _ => 0) (fun _ => 0) expCost toFunCost
      (by rfl)
      ⟨by dsimp only; omega, by dsimp only; omega⟩
  · dsimp only
    refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_mono (fun a ha => ?_) _
      (simProt_kdf_allRet _ x))
    exact ⟨by dsimp only; grind, by dsimp only; grind⟩

set_option maxHeartbeats 1600000 in
-- Eight event cases, each consumed node by node by `time_bound`.
/-- **Time of the `start` step of the costed X3DH simulator**: at most
`200 + 20 t_coe + 20 t_exp + 20 t_toFun` plus twenty units per entry of the key-derivation table
and per notice of the state. -/
theorem simProt.start.tree.timeBound_timed (G : PAKE.DHExtract.DHGroup S W) (coe : S ≃ W → S → W)
    (coeCost : S ≃ W → S → ℕ) (expCost : W → S → ℕ) (toFunCost : S → ℕ)
    (s : SimSt S W K) (e : OEv W) {tc te tf : ℕ} (hc : ∀ a b, coeCost a b ≤ tc)
    (he : ∀ a b, expCost a b ≤ te) (hf : ∀ a, toFunCost a ≤ tf) :
    SPTree.Timed.stepTime (simProt.start.tree.timed G coe coeCost s e expCost toFunCost) ≤
      200 + 20 * tc + 20 * te + 20 * tf + 20 * s.1.ro.length +
        20 * s.1.st.notices.length := by
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ | pid |
    ⟨sid, pid⟩ | ⟨sid, pid, e⟩ | x)
  · time_bound
  · time_bound
  · time_bound
  · time_bound
  · time_bound
  · time_bound
  · time_bound
  · have := start_complete_time G coe coeCost expCost toFunCost s sid pid hc he hf
    omega
  · have := start_send_time G coe coeCost expCost toFunCost s sid pid e hc he hf
    omega
  · time_bound

/-- **Graded running time of the costed X3DH simulator** on the invariant `SimInv`: after `i`
activations every step costs at most `a + 40 i`, with `a = 200 + 20 t_coe + 20 t_exp + 20 t_toFun`,
the growth coming from the key-derivation table and the notices, each of at most `i` entries. -/
theorem simProt.timeBoundGraded_timed (G : PAKE.DHExtract.DHGroup S W) (coe : S ≃ W → S → W)
    (coeCost : S ≃ W → S → ℕ) (expCost : W → S → ℕ) (toFunCost : S → ℕ) {tc te tf : ℕ}
    (hc : ∀ a b, coeCost a b ≤ tc) (he : ∀ a b, expCost a b ≤ te)
    (hf : ∀ a, toFunCost a ≤ tf) :
    (simProt.timed (K := K) G coe coeCost expCost toFunCost).TimeBoundGraded SimInv
      (200 + 20 * tc + 20 * te + 20 * tf) 40 := by
  refine ⟨⟨by simp [simProt.timed, rInit, UCTransparent.FAKE.initSt],
      by simp [simProt.timed, rInit, UCTransparent.FAKE.initSt]⟩, fun i s e hs => ⟨?_,
      simProt.start_allRet G coe coeCost expCost toFunCost s e hs⟩,
    fun i s o hs => ⟨?_, ?_⟩, fun i s o hs => ⟨?_, ?_⟩⟩
  · have := simProt.start.tree.timeBound_timed G coe coeCost expCost toFunCost s e hc he hf
    obtain ⟨h1, h2⟩ := hs
    simp only [simProt.timed, Prod.mk.eta]
    omega
  · have := simProt.resume.tree.timeBound_timed G coe coeCost s o hc
    simp only [simProt.timed, Prod.mk.eta]
    omega
  · obtain ⟨h1, h2⟩ := hs
    simp only [simProt.timed, simProt.resume.tree.timed]
    exact ⟨by dsimp only; omega, by dsimp only; omega⟩
  · have := simProt.finish.tree.timeBound_timed G coe coeCost s o hc
    simp only [simProt.timed, Prod.mk.eta]
    omega
  · obtain ⟨h1, h2⟩ := hs
    simp only [simProt.timed, simProt.finish.tree.timed]
    exact ⟨by dsimp only; omega, by dsimp only; omega⟩

end Time

derive_simulator x3dhSim

end CatCrypt.Crypto.AKE.X3DHSquare
