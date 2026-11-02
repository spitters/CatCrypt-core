/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.PQXDHSquare
public import CatCryptCore.Crypto.AKE.X3DHSquareTimed
public import CatCryptCore.Crypto.UCSimulatorTimed
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound

/-!
# Running time of the PQXDH simulator

`derive_reduction` builds the costed form `simProtK.timed` of the multi-call simulator
`simProtK O G` of `PQXDHSquare.lean` over the KEM operations `O` and its erasure theorem. Key
generation `O.keygen` and encapsulation `O.encaps` are priced by their cost companions, and
decapsulation `O.decaps` by its cost companion. The steps `ltStep` and `roStep` shared with X3DH
are the costed forms of `X3DHSquareTimed.lean`.

The key-derivation table and the list of notices grow by at most one entry per activation, and
every other table of the state starts each step at the zero cost companion. The invariant
`SimInv i` bounds the two lengths by `i` after `i` activations, so that a step costs at most
`a + 40 i` (`simProtK.timeBoundGraded_timed`), the graded form for a simulator whose state grows
with the activations, and `derive_simulator` lifts it to `pqxdhSimK` and `pqxdhSim`. The costed
form of `pqxdhSim P` takes costed key generation and encapsulation trees, and its erasure theorem
holds when they erase to the operations `kemOps P`.

No module imports this file.

## Main results

* `simProtK.timed`, `simProtK.erase_timed`: the costed multi-call simulator and its erasure.
* `simProtK.resume.tree.timeBound_timed`, `simProtK.finish.tree.timeBound_timed`: `resume` and
  `finish` cost at most two units.
* `simProtK.start_time`: the time of `start` on an event other than `complete` and `send`,
  linear in the time of key generation, the length of the key-derivation table and the number
  of notices.
* `simProtK.start.tree.timeBound_timed`: the time of `start` on every event.
* `simProtK.timeBoundGraded_timed`: its graded time bound on the invariant `SimInv`.
* `pqxdhSimK.timed`, `pqxdhSimK.erase_timed`, `pqxdhSimK.timeBoundGraded_timed` and
  `pqxdhSim.timed`, `pqxdhSim.erase_timed`, `pqxdhSim.timeBoundGraded_timed`: the costed bundled
  simulators, their erasure, and their graded time bounds.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.PQXDHSquare

open CatCrypt.Core

set_option maxHeartbeats 400000 in
-- The start step reflects thirteen event cases with nested record updates.
derive_reduction simProtK

derive_time_bound simProtK.resume.tree
derive_time_bound simProtK.finish.tree

section Time

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS]

/-- Whether an event of the real interface is `complete` or `send`, the two events on which the
simulator encapsulates or decapsulates. -/
def IsKemEvent : OEv W SS C → Bool
  | .inr (.complete _ _) | .inr (.send _ _ _ _) => true
  | _ => false

set_option maxHeartbeats 1600000 in
-- Eleven event cases, each consumed node by node by `time_bound`, above the default budget.
/-- **Time of the `start` step of the costed PQXDH simulator** on an event other than `complete`
and `send`: at most `100 + 20 t_coe + t_keygen` plus twenty units per entry of the
key-derivation table and per notice of the state, where `t_keygen` bounds the time of the
costed key generation. -/
theorem simProtK.start_time (O : KemOps PK SK SS C) (G : PAKE.DHExtract.DHGroup S W)
    (coe : S ≃ W → S → W) (coeCost : S ≃ W → S → ℕ) (decaps : SK → C → Option SS)
    (decapsCost : SK → C → ℕ) (keygen : SPTree.Timed (PK × SK))
    (encaps : PK → SPTree.Timed (SS × C)) (encapsCost : PK → ℕ) (expCost : W → S → ℕ)
    (toFunCost : S → ℕ) (s : SimSt S W K PK SK SS C) (e : OEv W SS C) (he : IsKemEvent e = false)
    {t_coeCost t_keygen : ℕ} (hcoe : ∀ a b, coeCost a b ≤ t_coeCost)
    (hkg : keygen.time ≤ t_keygen) :
    SPTree.Timed.stepTime
        (simProtK.start.tree.timed O G coe coeCost decaps decapsCost keygen encaps encapsCost s e
          expCost toFunCost) ≤
      100 + 20 * t_coeCost + t_keygen + 20 * s.1.ro.length + 20 * s.1.x.st.notices.length := by
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ |
    ⟨sid, pid⟩ | pid | ⟨sid, pid⟩ | ⟨sid, pid, e, c⟩ | x)
  · time_bound
  · time_bound
  · time_bound
  · time_bound
  · time_bound
  · time_bound
  · time_bound
  · time_bound
  · simp [IsKemEvent] at he
  · simp [IsKemEvent] at he
  · time_bound

-- The costed steps of `simProtK` are compiled through the auxiliary matchers of its source, and
-- the bounds below unfold them by name.
set_option linter.auxLemma false

open SPTree.Timed (stepTime_bind_bind_le stepTime_pair stepTime_delay_bind_const_le
  stepTime_cost_le)

/-- The costed state of the simulator: the costed copy of the X3DH state, the KEM key pairs and
the encapsulations with their cost companions, the table of the key derivation, the table of
inputs with its cost companion, and the phase. -/
abbrev SimHat (S W K PK SK SS C : Type) : Type :=
  (X3DHSquare.RHat S W K ×
    ((UCTransparent.FAKE.Inst → Option (PK × SK)) × (UCTransparent.FAKE.Inst → ℕ)) ×
    ((UCTransparent.FAKE.Inst → Option C) × (UCTransparent.FAKE.Inst → ℕ)) ×
    List (PInp W SS × K)) ×
  ((UCTransparent.FAKE.Inst → Option (PInp W SS)) × (UCTransparent.FAKE.Inst → ℕ)) ×
    Phase S W K PK C

omit [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] [DecidableEq SS] in
/-- The first lookup of long-term secrets in `complete` and `send` costs at most `3 + T` when
the cost companion of the secrets is at most `T`. -/
theorem lt1_time (s : SimHat S W K PK SK SS C) (sid : UCTransparent.FAKE.SessionId)
    (pid : UCTransparent.FAKE.PartyId) {T : ℕ} (hc : ∀ p, s.1.1.2.1.2 p ≤ T) :
    SPTree.Timed.stepTime (simProtK.start.tree.match_3.timed s sid pid s.1.1.2.1.2) ≤ 3 + T := by
  have := hc pid
  simp only [simProtK.start.tree.match_3.timed, SPTree.Timed.stepTime]
  split <;> simp only [SPTree.Timed.time_ret, SPTree.Timed.time_sample] <;>
    grind [Finset.sup_eq_bot_iff, Nat.bot_eq_zero]

omit [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] [DecidableEq SS] in
/-- The first lookup of long-term secrets keeps the notices and raises the cost companion of the
secrets by at most three. -/
theorem lt1_allRet (s : SimHat S W K PK SK SS C) (sid : UCTransparent.FAKE.SessionId)
    (pid : UCTransparent.FAKE.PartyId) {T : ℕ} (hc : ∀ p, s.1.1.2.1.2 p ≤ T) :
    SPTree.Timed.AllRet (fun y => y.2.1.2.2.1 = s.1.1.1.2.2.1 ∧ ∀ p, y.2.2.1.2 p ≤ T + 3)
      (simProtK.start.tree.match_3.timed s sid pid s.1.1.2.1.2).2 := by
  simp only [simProtK.start.tree.match_3.timed]
  split
  · exact ⟨rfl, fun p => by have := hc p; grind⟩
  · intro b
    refine ⟨rfl, fun p => ?_⟩
    have := hc p
    dsimp only
    split <;> omega

omit [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] [DecidableEq SS] in
/-- The second lookup of long-term secrets costs at most `3 + T` when the cost companion of the
secrets is at most `T`. -/
theorem lt2_time (r : UCTransparent.FAKE.Rec K) (x : (S × S) × X3DHSquare.RSt S W K)
    (h : X3DHSquare.RHat S W K) {T : ℕ} (hc : ∀ p, h.2.1.2 p ≤ T) :
    SPTree.Timed.stepTime (simProtK.start.tree.match_4.timed r x h) ≤ 3 + T := by
  have := hc r.peer
  simp only [simProtK.start.tree.match_4.timed, SPTree.Timed.stepTime, SPTree.Timed.delay]
  split <;> simp only [SPTree.Timed.time_ret, SPTree.Timed.time_sample] <;>
    grind [Finset.sup_eq_bot_iff, Nat.bot_eq_zero]

omit [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] [DecidableEq SS] in
/-- The second lookup of long-term secrets keeps the notices. -/
theorem lt2_allRet (r : UCTransparent.FAKE.Rec K) (x : (S × S) × X3DHSquare.RSt S W K)
    (h : X3DHSquare.RHat S W K) :
    SPTree.Timed.AllRet (fun y => y.2.1.2.2.1 = x.2.st.notices)
      (simProtK.start.tree.match_4.timed r x h).2 := by
  simp only [simProtK.start.tree.match_4.timed, SPTree.Timed.delay]
  split
  · exact rfl
  · exact fun _ => rfl

omit [Fintype S] [Inhabited K] in
/-- The key derivation at the input of the initiator in `complete` costs at most
`12 + 3 t_toFun + 4 t_exp + 5 L` on a table of length `L`. -/
theorem kdfIni_time (G : PAKE.DHExtract.DHGroup S W) (s : SimHat S W K PK SK SS C)
    (sid : UCTransparent.FAKE.SessionId) (pid : UCTransparent.FAKE.PartyId)
    (r : UCTransparent.FAKE.Rec K) (ek opk : S) (x y : (S × S) × X3DHSquare.RSt S W K)
    (z : SS × C) (toFunCost : S → ℕ) (expCost : W → S → ℕ) {te tf : ℕ}
    (he : ∀ a b, expCost a b ≤ te) (hf : ∀ a, toFunCost a ≤ tf) :
    SPTree.Timed.stepTime
        (simProtK.start.tree.match_5.timed G s sid pid r ek opk x y z toFunCost expCost) ≤
      12 + 3 * tf + 4 * te + 5 * s.1.2.2.2.length := by
  have hl := fun a => List.lookup.timedCost_le a s.1.2.2.2
  simp only [simProtK.start.tree.match_5.timed, SPTree.Timed.stepTime]
  split <;> simp only [SPTree.Timed.time_ret, SPTree.Timed.time_sample] <;>
    grind [Finset.sup_eq_bot_iff, Nat.bot_eq_zero]

omit [Fintype S] [Inhabited K] in
/-- The key derivation at the input of the initiator adds at most one entry to the table. -/
theorem kdfIni_allRet (G : PAKE.DHExtract.DHGroup S W) (s : SimHat S W K PK SK SS C)
    (sid : UCTransparent.FAKE.SessionId) (pid : UCTransparent.FAKE.PartyId)
    (r : UCTransparent.FAKE.Rec K) (ek opk : S) (x y : (S × S) × X3DHSquare.RSt S W K)
    (z : SS × C) (toFunCost : S → ℕ) (expCost : W → S → ℕ) :
    SPTree.Timed.AllRet (fun w => w.2.length ≤ s.1.2.2.2.length + 1)
      (simProtK.start.tree.match_5.timed G s sid pid r ek opk x y z toFunCost expCost).2 := by
  simp only [simProtK.start.tree.match_5.timed]
  split
  · exact Nat.le_succ _
  · exact fun _ => le_rfl

/-- The `complete` step of the costed simulator (`simComplete`), from a costed state whose cost
companions of the long-term secrets, the key pairs and the inputs vanish, costs at most
`65 + 3 t_coe + 3 t_toFun + 8 t_exp + t_encC + t_enc + 5 L` on a key-derivation table of length
`L`. -/
theorem complete_time (G : PAKE.DHExtract.DHGroup S W) (s : SimHat S W K PK SK SS C)
    (encaps : PK → SPTree.Timed (SS × C)) (encapsCost : PK → ℕ) (coe : S ≃ W → S → W)
    (coeCost : S ≃ W → S → ℕ) (sid : UCTransparent.FAKE.SessionId)
    (pid : UCTransparent.FAKE.PartyId) (expCost : W → S → ℕ) (toFunCost : S → ℕ)
    (hlt : s.1.1.2.1.2 = fun _ => 0) (hkem : s.1.2.1.2 = fun _ => 0)
    (hinp : s.2.1.2 = fun _ => 0) {tc te tf tenc tec : ℕ}
    (hc : ∀ a b, coeCost a b ≤ tc) (he : ∀ a b, expCost a b ≤ te)
    (hf : ∀ a, toFunCost a ≤ tf) (henc : ∀ pk, (encaps pk).time ≤ tenc)
    (hec : ∀ pk, encapsCost pk ≤ tec) :
    SPTree.Timed.stepTime (simProtK.start.tree.match_7.timed G s encaps encapsCost coe coeCost
        sid pid (fun _ => 0) (fun _ => 0) expCost toFunCost) ≤
      65 + 3 * tc + 3 * tf + 8 * te + tec + tenc + 5 * s.1.2.2.2.length := by
  simp only [simProtK.start.tree.match_7.timed]
  split
  · rename_i _ _ r ek _ _
    simp only [simProtK.start.tree.match_6.timed, hkem]
    rw [stepTime_pair, SPTree.Timed.stepTime_delay, stepTime_pair]
    rcases hO : X3DHSquare.opkOf (⟨⟨s.1.1.1.1.1, s.1.1.1.2.1.1, s.1.1.1.2.2.1, s.1.1.1.2.2.2⟩,
        s.1.1.2.1.1, s.1.1.2.2.1.1, s.1.1.2.2.2⟩ : X3DHSquare.RSt S W K) sid r.peer with
      _ | opk <;>
    rcases hP : pkOf (⟨⟨⟨s.1.1.1.1.1, s.1.1.1.2.1.1, s.1.1.1.2.2.1, s.1.1.1.2.2.2⟩,
        s.1.1.2.1.1, s.1.1.2.2.1.1, s.1.1.2.2.2⟩, s.1.2.1.1, s.1.2.2.1.1, s.1.2.2.2⟩ :
          PSt S W K PK SK SS C) sid r.peer with _ | pk
    · simp only [SPTree.Timed.stepTime, SPTree.Timed.time_ret]
      split <;> (try split_ifs) <;> omega
    · simp only [SPTree.Timed.stepTime, SPTree.Timed.time_ret]
      split <;> (try split_ifs) <;> omega
    · simp only [SPTree.Timed.stepTime, SPTree.Timed.time_ret]
      split <;> (try split_ifs) <;> omega
    · simp only [SPTree.Timed.stepTime_delay]
      split_ifs
      · refine le_trans (Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_left
          (Nat.add_le_add_left (stepTime_bind_bind_le 1 1 _ _ _
            (lt1_time s sid pid (T := 0) fun p => by simp [hlt])
            (lt1_allRet s sid pid (T := 0) fun p => by simp [hlt])
            (fun a ha => lt2_time r _ a.2 (T := 0 + 3) ha.2)
            (fun a _ => lt2_allRet r _ a.2)
            (TF := 1 + tec + (tenc + (7 + 3 * tc + 4 * te + 1 +
              (16 + 3 * tf + 4 * te + 5 * s.1.2.2.2.length))))
            ?_) 3) _) 1) _) ?_
        · intro a b _ _
          rw [SPTree.Timed.stepTime_delay]
          refine le_trans (Nat.add_le_add_left (SPTree.Timed.stepTime_bind_le _ _
            (7 + 3 * tc + 4 * te + 1 + (16 + 3 * tf + 4 * te + 5 * s.1.2.2.2.length))
            fun kc => ?_) _) ?_
          · refine le_trans (stepTime_cost_le _ _ (TC := 7 + 3 * tc + 4 * te)
              (TD := 16 + 3 * tf + 4 * te + 5 * s.1.2.2.2.length) ?_ ?_) le_rfl
            · grind
            · split_ifs
              · refine le_trans (stepTime_delay_bind_const_le 1 3 _ _
                  (kdfIni_time G s sid pid r ek opk _ _ kc toFunCost expCost he hf)) ?_
                omega
              all_goals
                simp only [SPTree.Timed.stepTime, SPTree.Timed.time_ret, hinp]
                split <;> omega
          · have := henc (pk)
            have := hec (pk)
            omega
        · split <;> (try split_ifs) <;> omega
      · simp only [SPTree.Timed.stepTime, SPTree.Timed.time_ret]
        split <;> (try split_ifs) <;> omega
  · simp only [SPTree.Timed.stepTime, SPTree.Timed.time_ret]
    omega

omit [Fintype S] [Inhabited K] in
/-- The key derivation at the input of the responder in `send` costs at most
`12 + 3 t_toFun + 4 t_exp + 5 L` on a table of length `L`. -/
theorem kdfRes_time (G : PAKE.DHExtract.DHGroup S W) (s : SimHat S W K PK SK SS C)
    (sid : UCTransparent.FAKE.SessionId) (pid : UCTransparent.FAKE.PartyId) (e : W)
    (r : UCTransparent.FAKE.Rec K) (opk : S) (ss : SS) (x y : (S × S) × X3DHSquare.RSt S W K)
    (toFunCost : S → ℕ) (expCost : W → S → ℕ) {te tf : ℕ}
    (he : ∀ a b, expCost a b ≤ te) (hf : ∀ a, toFunCost a ≤ tf) :
    SPTree.Timed.stepTime
        (simProtK.start.tree.match_10.timed G s sid pid e r opk ss x y toFunCost expCost) ≤
      12 + 3 * tf + 4 * te + 5 * s.1.2.2.2.length := by
  have hl := fun a => List.lookup.timedCost_le a s.1.2.2.2
  simp only [simProtK.start.tree.match_10.timed, SPTree.Timed.stepTime]
  split <;> simp only [SPTree.Timed.time_ret, SPTree.Timed.time_sample] <;>
    grind [Finset.sup_eq_bot_iff, Nat.bot_eq_zero]

omit [Fintype S] [Inhabited K] in
/-- The key derivation at the input of the responder adds at most one entry to the table. -/
theorem kdfRes_allRet (G : PAKE.DHExtract.DHGroup S W) (s : SimHat S W K PK SK SS C)
    (sid : UCTransparent.FAKE.SessionId) (pid : UCTransparent.FAKE.PartyId) (e : W)
    (r : UCTransparent.FAKE.Rec K) (opk : S) (ss : SS) (x y : (S × S) × X3DHSquare.RSt S W K)
    (toFunCost : S → ℕ) (expCost : W → S → ℕ) :
    SPTree.Timed.AllRet (fun w => w.2.length ≤ s.1.2.2.2.length + 1)
      (simProtK.start.tree.match_10.timed G s sid pid e r opk ss x y toFunCost expCost).2 := by
  simp only [simProtK.start.tree.match_10.timed]
  split
  · exact Nat.le_succ _
  · exact fun _ => le_rfl

/-- The `send` step of the costed simulator (`simSend`), from a costed state whose cost
companions of the long-term secrets and the inputs vanish, costs at most
`65 + 3 t_coe + 3 t_toFun + 8 t_exp + t_dec + 5 L` on a key-derivation table of length `L`. -/
theorem send_time (G : PAKE.DHExtract.DHGroup S W) (s : SimHat S W K PK SK SS C)
    (coe : S ≃ W → S → W) (coeCost : S ≃ W → S → ℕ) (decaps : SK → C → Option SS)
    (decapsCost : SK → C → ℕ) (sid : UCTransparent.FAKE.SessionId)
    (pid : UCTransparent.FAKE.PartyId) (e : W) (c : C) (expCost : W → S → ℕ)
    (toFunCost : S → ℕ) (hlt : s.1.1.2.1.2 = fun _ => 0) (hinp : s.2.1.2 = fun _ => 0)
    {tc te tf tdc : ℕ} (hc : ∀ a b, coeCost a b ≤ tc) (he : ∀ a b, expCost a b ≤ te)
    (hf : ∀ a, toFunCost a ≤ tf) (hdc : ∀ a b, decapsCost a b ≤ tdc) :
    SPTree.Timed.stepTime (simProtK.start.tree.match_12.timed G s coe coeCost decaps decapsCost
        sid pid e c (fun _ => 0) (fun _ => 0) (fun _ => 0) expCost toFunCost) ≤
      65 + 3 * tc + 3 * tf + 8 * te + tdc + 5 * s.1.2.2.2.length := by
  simp only [simProtK.start.tree.match_12.timed]
  split
  · rename_i _ _ _ r opk kp _ _ _
    simp only [simProtK.start.tree.match_11.timed,
      show @simProtK.start.tree.match_8.timed S W K PK SK SS C _ _ =
        @simProtK.start.tree.match_3.timed S W K PK SK SS C _ _ from rfl,
      show @simProtK.start.tree.match_9.timed S W K _ _ =
        @simProtK.start.tree.match_4.timed S W K _ _ from rfl]
    rw [stepTime_pair, SPTree.Timed.stepTime_delay, stepTime_pair]
    have hd := hdc kp.2 c
    rcases hD : decaps kp.2 c with _ | ss
    · simp only [SPTree.Timed.stepTime, SPTree.Timed.time_ret]
      omega
    · simp only [SPTree.Timed.stepTime_delay]
      split_ifs
      · refine le_trans (Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_left
          (Nat.add_le_add_left (stepTime_bind_bind_le 1 1 _ _ _
            (lt1_time s sid pid (T := 0) fun p => by simp [hlt])
            (lt1_allRet s sid pid (T := 0) fun p => by simp [hlt])
            (fun a ha => lt2_time r _ a.2 (T := 0 + 3) ha.2)
            (fun a _ => lt2_allRet r _ a.2)
            (TF := 7 + 3 * tc + 4 * te + 1 + (16 + 3 * tf + 4 * te + 5 * s.1.2.2.2.length))
            ?_) 3) _) 1) _) ?_
        · intro a b _ _
          refine le_trans (stepTime_cost_le _ _ (TC := 7 + 3 * tc + 4 * te)
            (TD := 16 + 3 * tf + 4 * te + 5 * s.1.2.2.2.length) ?_ ?_) le_rfl
          · grind
          · split_ifs
            · refine le_trans (stepTime_delay_bind_const_le 1 3 _ _
                (kdfRes_time G s sid pid e r opk ss _ _ toFunCost expCost he hf)) ?_
              omega
            all_goals
              simp only [SPTree.Timed.stepTime, SPTree.Timed.time_ret, hinp]
              split <;> omega
        · omega
      · simp only [SPTree.Timed.stepTime, SPTree.Timed.time_ret]
        omega
  · simp only [SPTree.Timed.stepTime, SPTree.Timed.time_ret]
    omega

/-- The invariant of the costed state after `i` activations: the table of the key derivation
and the list of notices have at most `i` entries. -/
def HatInv (i : ℕ) (y : SimHat S W K PK SK SS C) : Prop :=
  y.1.2.2.2.length ≤ i ∧ y.1.1.1.2.2.1.length ≤ i

/-- The invariant of the state of the simulator after `i` activations: the table of the key
derivation and the list of notices have at most `i` entries. -/
def SimInv (i : ℕ) (s : SimSt S W K PK SK SS C) : Prop :=
  s.1.ro.length ≤ i ∧ s.1.x.st.notices.length ≤ i

omit [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] [DecidableEq SS] in
/-- The lookup of long-term secrets at `pub` keeps the notices and the key-derivation table. -/
theorem lt0_allRet (s : SimHat S W K PK SK SS C) (pid : UCTransparent.FAKE.PartyId) :
    SPTree.Timed.AllRet (fun y => y.2.1.2.2.1 = s.1.1.1.2.2.1)
      (simProtK.start.tree.match_1.timed s pid s.1.1.2.1.2).2 := by
  simp only [simProtK.start.tree.match_1.timed]
  split
  · exact rfl
  · exact fun _ => rfl

omit [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] [DecidableEq SS] in
/-- The lookup of long-term secrets at `corrupt` keeps the notices and the key-derivation
table. -/
theorem lt0_allRet' (s : SimHat S W K PK SK SS C) (pid : UCTransparent.FAKE.PartyId) :
    SPTree.Timed.AllRet (fun y => y.2.1.2.2.1 = s.1.1.1.2.2.1)
      (simProtK.start.tree.match_2.timed s pid s.1.1.2.1.2).2 := by
  simp only [simProtK.start.tree.match_2.timed]
  split
  · exact rfl
  · exact fun _ => rfl

omit [Field S] [Fintype S] [Inhabited K] in
/-- A query of the key derivation adds at most one entry to the table. -/
theorem kdf_allRet (s : SimHat S W K PK SK SS C) (x : PInp W SS) :
    SPTree.Timed.AllRet (fun z => z.2.length ≤ s.1.2.2.2.length + 1)
      (simProtK.start.tree.match_13.timed s x).2 := by
  simp only [simProtK.start.tree.match_13.timed]
  split
  · exact Nat.le_succ _
  · exact fun _ => le_rfl

/-- The `complete` step preserves the invariant, one activation later. -/
theorem complete_allRet (G : PAKE.DHExtract.DHGroup S W) (s : SimHat S W K PK SK SS C)
    (encaps : PK → SPTree.Timed (SS × C)) (encapsCost : PK → ℕ) (coe : S ≃ W → S → W)
    (coeCost : S ≃ W → S → ℕ) (sid : UCTransparent.FAKE.SessionId)
    (pid : UCTransparent.FAKE.PartyId) (rc ec : UCTransparent.FAKE.Inst → ℕ)
    (expCost : W → S → ℕ) (toFunCost : S → ℕ) (hlt : s.1.1.2.1.2 = fun _ => 0) {i : ℕ}
    (hx : HatInv i s) :
    SPTree.Timed.AllRet (fun y => HatInv (i + 1) y.1)
      (simProtK.start.tree.match_7.timed G s encaps encapsCost coe coeCost sid pid rc ec expCost
        toFunCost).2 := by
  obtain ⟨hro, hn⟩ := hx
  have hs : HatInv (i + 1) s := ⟨by omega, by omega⟩
  simp only [simProtK.start.tree.match_7.timed]
  split
  · rename_i _ _ r ek _ _
    simp only [simProtK.start.tree.match_6.timed, SPTree.Timed.delay]
    split
    · split_ifs
      · refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_mono (fun a ha => ?_) _
          (lt1_allRet s sid pid (T := 0) fun p => by simp [hlt]))
        refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_mono (fun b hb => ?_) _
          (lt2_allRet r _ a.2))
        dsimp only at hb
        refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_of_forall (fun kc => ?_) _)
        split_ifs
        · refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_mono (fun z hz => ?_) _
            (kdfIni_allRet G s sid pid r ek _ _ _ kc toFunCost expCost))
          exact ⟨by dsimp only; grind, by dsimp only; grind⟩
        all_goals exact ⟨by dsimp only; grind, by dsimp only; grind⟩
      · exact hs
    · exact hs
  · exact hs

/-- The `send` step preserves the invariant, one activation later. -/
theorem send_allRet (G : PAKE.DHExtract.DHGroup S W) (s : SimHat S W K PK SK SS C)
    (coe : S ≃ W → S → W) (coeCost : S ≃ W → S → ℕ) (decaps : SK → C → Option SS)
    (decapsCost : SK → C → ℕ) (sid : UCTransparent.FAKE.SessionId)
    (pid : UCTransparent.FAKE.PartyId) (e : W) (c : C) (rc ec kc : UCTransparent.FAKE.Inst → ℕ)
    (expCost : W → S → ℕ) (toFunCost : S → ℕ) (hlt : s.1.1.2.1.2 = fun _ => 0) {i : ℕ}
    (hx : HatInv i s) :
    SPTree.Timed.AllRet (fun y => HatInv (i + 1) y.1)
      (simProtK.start.tree.match_12.timed G s coe coeCost decaps decapsCost sid pid e c rc ec kc
        expCost toFunCost).2 := by
  obtain ⟨hro, hn⟩ := hx
  have hs : HatInv (i + 1) s := ⟨by omega, by omega⟩
  simp only [simProtK.start.tree.match_12.timed]
  split
  · rename_i _ _ _ r opk kp _ _ _
    simp only [simProtK.start.tree.match_11.timed, SPTree.Timed.delay,
      show @simProtK.start.tree.match_8.timed S W K PK SK SS C _ _ =
        @simProtK.start.tree.match_3.timed S W K PK SK SS C _ _ from rfl,
      show @simProtK.start.tree.match_9.timed S W K _ _ =
        @simProtK.start.tree.match_4.timed S W K _ _ from rfl]
    split
    · rename_i ss _
      split_ifs
      · refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_mono (fun a ha => ?_) _
          (lt1_allRet s sid pid (T := 0) fun p => by simp [hlt]))
        refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_mono (fun b hb => ?_) _
          (lt2_allRet r _ a.2))
        dsimp only at hb
        split_ifs
        · refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_mono (fun z hz => ?_) _
            (kdfRes_allRet G s sid pid e r opk ss _ _ toFunCost expCost))
          exact ⟨by dsimp only; grind, by dsimp only; grind⟩
        all_goals exact ⟨by dsimp only; grind, by dsimp only; grind⟩
      · exact hs
    · exact hs
  · exact hs

/-- The `start` step preserves the invariant, one activation later. -/
theorem simProtK.start_allRet (O : KemOps PK SK SS C) (G : PAKE.DHExtract.DHGroup S W)
    (coe : S ≃ W → S → W) (coeCost : S ≃ W → S → ℕ) (decaps : SK → C → Option SS)
    (decapsCost : SK → C → ℕ) (keygen : SPTree.Timed (PK × SK))
    (encaps : PK → SPTree.Timed (SS × C)) (encapsCost : PK → ℕ) (expCost : W → S → ℕ)
    (toFunCost : S → ℕ) (s : SimSt S W K PK SK SS C) (e : OEv W SS C) {i : ℕ}
    (hs : SimInv i s) :
    SPTree.Timed.AllRet (fun y => SimInv (i + 1) y.1)
      (simProtK.start.tree.timed O G coe coeCost decaps decapsCost keygen encaps encapsCost s e
        expCost toFunCost).2 := by
  obtain ⟨hro, hn⟩ := hs
  simp only [simProtK.start.tree.timed, SPTree.Timed.delay]
  refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_mono
    (Q := fun y : SimHat S W K PK SK SS C × Dec S W K PK C => HatInv (i + 1) y.1)
    (fun y hy => hy) _ ?_)
  simp only [simProtK.start.tree.match_14.timed, SPTree.Timed.delay]
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ |
    ⟨sid, pid⟩ | pid | ⟨sid, pid⟩ | ⟨sid, pid, e, c⟩ | x)
  · dsimp only
    split_ifs
    all_goals first
      | exact ⟨by dsimp only; omega, by dsimp only; omega⟩
      | exact fun _ => ⟨by dsimp only; omega, by dsimp only; omega⟩
      | exact fun _ => ⟨by dsimp only; omega, by
          dsimp only
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega⟩
      | exact fun _ => SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_of_forall
          (fun _ => ⟨by dsimp only; omega, by dsimp only; omega⟩) _)
      | exact fun _ => SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_of_forall
          (fun _ => ⟨by dsimp only; omega, by
            dsimp only
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega⟩) _)
  · exact ⟨by dsimp only; omega, by dsimp only; omega⟩
  · exact ⟨by dsimp only; omega, by dsimp only; omega⟩
  · refine ⟨by dsimp only; omega, ?_⟩
    dsimp only
    split <;> dsimp only <;> omega
  · dsimp only
    refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_mono (fun a ha => ?_) _
      (lt0_allRet _ pid))
    exact ⟨by dsimp only; grind, by dsimp only; grind⟩
  · exact ⟨by dsimp only; omega, by dsimp only; omega⟩
  · exact ⟨by dsimp only; omega, by dsimp only; omega⟩
  · dsimp only
    split_ifs
    · exact ⟨by dsimp only; omega, by dsimp only; omega⟩
    · refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_mono (fun a ha => ?_) _
        (lt0_allRet' _ pid))
      exact ⟨by dsimp only; grind, by dsimp only; grind⟩
  · exact complete_allRet G _ encaps encapsCost coe coeCost sid pid (fun _ => 0) (fun _ => 0)
      expCost toFunCost (by rfl) ⟨by dsimp only; omega, by dsimp only; omega⟩
  · exact send_allRet G _ coe coeCost decaps decapsCost sid pid e c (fun _ => 0) (fun _ => 0)
      (fun _ => 0) expCost toFunCost (by rfl) ⟨by dsimp only; omega, by dsimp only; omega⟩
  · dsimp only
    refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_mono (fun a ha => ?_) _
      (kdf_allRet _ x))
    exact ⟨by dsimp only; grind, by dsimp only; grind⟩

/-- **Time of the `start` step of the costed PQXDH simulator**: at most
`100 + 20 t_coe + 8 t_exp + 3 t_toFun + t_keygen + t_encC + t_enc + t_dec` plus twenty units per
entry of the key-derivation table and per notice of the state. -/
theorem simProtK.start.tree.timeBound_timed (O : KemOps PK SK SS C)
    (G : PAKE.DHExtract.DHGroup S W) (coe : S ≃ W → S → W) (coeCost : S ≃ W → S → ℕ)
    (decaps : SK → C → Option SS) (decapsCost : SK → C → ℕ) (keygen : SPTree.Timed (PK × SK))
    (encaps : PK → SPTree.Timed (SS × C)) (encapsCost : PK → ℕ) (expCost : W → S → ℕ)
    (toFunCost : S → ℕ) (s : SimSt S W K PK SK SS C) (e : OEv W SS C)
    {tc te tf tk tenc tec tdc : ℕ} (hc : ∀ a b, coeCost a b ≤ tc)
    (he : ∀ a b, expCost a b ≤ te) (hf : ∀ a, toFunCost a ≤ tf) (hkg : keygen.time ≤ tk)
    (henc : ∀ pk, (encaps pk).time ≤ tenc) (hec : ∀ pk, encapsCost pk ≤ tec)
    (hdc : ∀ a b, decapsCost a b ≤ tdc) :
    SPTree.Timed.stepTime (simProtK.start.tree.timed O G coe coeCost decaps decapsCost keygen
        encaps encapsCost s e expCost toFunCost) ≤
      100 + 20 * tc + 8 * te + 3 * tf + tk + tec + tenc + tdc + 20 * s.1.ro.length +
        20 * s.1.x.st.notices.length := by
  have hn : IsKemEvent e = false → _ := fun h =>
    simProtK.start_time O G coe coeCost decaps decapsCost keygen encaps encapsCost expCost
      toFunCost s e h hc hkg
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ |
    ⟨sid, pid⟩ | pid | ⟨sid, pid⟩ | ⟨sid, pid, e, c⟩ | x)
  · have := hn rfl
    omega
  · have := hn rfl
    omega
  · have := hn rfl
    omega
  · have := hn rfl
    omega
  · have := hn rfl
    omega
  · have := hn rfl
    omega
  · have := hn rfl
    omega
  · have := hn rfl
    omega
  · simp only [simProtK.start.tree.timed]
    rw [SPTree.Timed.stepTime_delay]
    refine le_trans (SPTree.Timed.bind_ret_stepTime_le _ _) ?_
    simp only [SPTree.Timed.stepTime_delay, simProtK.start.tree.match_14.timed]
    rw [stepTime_pair]
    refine le_trans (Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_left
      (complete_time G _ encaps encapsCost coe coeCost sid pid expCost toFunCost (by rfl)
        (by rfl) (by rfl) hc he hf henc hec) _) _) _) ?_
    dsimp only
    omega
  · simp only [simProtK.start.tree.timed]
    rw [SPTree.Timed.stepTime_delay]
    refine le_trans (SPTree.Timed.bind_ret_stepTime_le _ _) ?_
    simp only [SPTree.Timed.stepTime_delay, simProtK.start.tree.match_14.timed]
    rw [stepTime_pair]
    refine le_trans (Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_left
      (send_time G _ coe coeCost decaps decapsCost sid pid e c expCost toFunCost (by rfl)
        (by rfl) hc he hf hdc) _) _) _) ?_
    dsimp only
    omega
  · have := hn rfl
    omega

/-- **Graded running time of the costed PQXDH simulator** on the invariant `SimInv`: after `i`
activations every step costs at most `a + 40 i`, with
`a = 100 + 20 t_coe + 8 t_exp + 3 t_toFun + t_keygen + t_encC + t_enc + t_dec`, the growth coming
from the key-derivation table and the notices, each of at most `i` entries. -/
theorem simProtK.timeBoundGraded_timed (O : KemOps PK SK SS C)
    (G : PAKE.DHExtract.DHGroup S W) (coe : S ≃ W → S → W) (coeCost : S ≃ W → S → ℕ)
    (decaps : SK → C → Option SS) (decapsCost : SK → C → ℕ) (keygen : SPTree.Timed (PK × SK))
    (encaps : PK → SPTree.Timed (SS × C)) (encapsCost : PK → ℕ) (expCost : W → S → ℕ)
    (toFunCost : S → ℕ) {tc te tf tk tenc tec tdc : ℕ} (hc : ∀ a b, coeCost a b ≤ tc)
    (he : ∀ a b, expCost a b ≤ te) (hf : ∀ a, toFunCost a ≤ tf) (hkg : keygen.time ≤ tk)
    (henc : ∀ pk, (encaps pk).time ≤ tenc) (hec : ∀ pk, encapsCost pk ≤ tec)
    (hdc : ∀ a b, decapsCost a b ≤ tdc) :
    (simProtK.timed (K := K) O G coe coeCost decaps decapsCost keygen encaps encapsCost expCost
      toFunCost).TimeBoundGraded SimInv
      (100 + 20 * tc + 8 * te + 3 * tf + tk + tec + tenc + tdc) 40 := by
  refine ⟨⟨by simp [simProtK.timed, pInit], by
        simp [simProtK.timed, pInit, X3DHSquare.rInit, UCTransparent.FAKE.initSt]⟩,
      fun i s e hs => ⟨?_, simProtK.start_allRet O G coe coeCost decaps decapsCost keygen encaps
        encapsCost expCost toFunCost s e hs⟩,
    fun i s o hs => ⟨?_, ?_⟩, fun i s o hs => ⟨?_, ?_⟩⟩
  · have := simProtK.start.tree.timeBound_timed O G coe coeCost decaps decapsCost keygen encaps
      encapsCost expCost toFunCost s e hc he hf hkg henc hec hdc
    obtain ⟨h1, h2⟩ := hs
    simp only [simProtK.timed, Prod.mk.eta]
    omega
  · have := simProtK.resume.tree.timeBound_timed O G coe coeCost decaps decapsCost keygen encaps
      encapsCost s o hc hdc hkg henc hec
    simp only [simProtK.timed, Prod.mk.eta]
    omega
  · obtain ⟨h1, h2⟩ := hs
    simp only [simProtK.timed, simProtK.resume.tree.timed]
    exact ⟨by dsimp only; omega, by dsimp only; omega⟩
  · have := simProtK.finish.tree.timeBound_timed O G coe coeCost decaps decapsCost keygen encaps
      encapsCost s o hc hdc hkg henc hec
    simp only [simProtK.timed, Prod.mk.eta]
    omega
  · obtain ⟨h1, h2⟩ := hs
    simp only [simProtK.timed, simProtK.finish.tree.timed]
    exact ⟨by dsimp only; omega, by dsimp only; omega⟩

end Time

derive_simulator pqxdhSimK

derive_simulator pqxdhSim

end CatCrypt.Crypto.AKE.PQXDHSquare
