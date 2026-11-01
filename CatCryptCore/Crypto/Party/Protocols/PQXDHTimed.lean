/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Party.Protocols.PQXDH
public import CatCryptCore.Crypto.Party.LoopTimed
public import CatCryptCore.Tactics.DeriveSimulator

/-!
# Running time of the PQXDH program simulator

`derive_simulator` builds the costed form of the PQXDH program simulator `pqxdhSimP Pk G`, the
loop `simLoop (kemOps Pk) G` of the simulator program `simBody`, on the costed loop
`Prog.loopMulti.timed`. Its costed body is the priced program `simBodyT` of `PQXDH.lean`, which
charges the length of the key-derivation table per iteration. The operations of `simBody O G`
are uniform samples and the key generation and encapsulation of the KEM, which do not touch the
heap (`KemOps.keygen_pureNF`, `KemOps.encaps_pureNF`), so they are distribution samples
(`simBody_allOps`). Under the tree interpretation of samples `ProgE.sampleTree` the costed body
erases to `simBody O G`, and its graded bound `8`, `1` gives the simulator the graded time bound
`17`, `2`: the `j`-th activation costs at most `17 + 2 j`.

No module imports this file.

## Main results

* `pqxdhSimP.timed`, `pqxdhSimP.erase_timed`, `pqxdhSimP.timeBoundGraded_timed`: the costed form
  of the simulator by `derive_simulator`.
* `simBody_allOps`: every operation of the simulator program is a distribution sample.
* `pqxdhSimP_timeCertificate`: the costed simulator erases to `pqxdhSimP Pk G`, and its `j`-th
  activation costs at most `17 + 2 j`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Party.Protocols.PQXDH

open CatCrypt.Core CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.AKE.PQXDHSquare
open CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.AKE.X3DHSquare (RSt)
open CatCrypt.Crypto.PAKE.DHExtract Prog

/-- A mapped computation that does not touch the heap is a distribution sample. -/
theorem isSample_map_of_isPure {γ : Type} {c : SPComp γ} (h : SPComp.IsPure c) (f : γ → ℕ) :
    ProgE.IsSample (SPComp.map f c) := by
  obtain ⟨d, hd⟩ := h
  have : c = liftSDistr d := funext hd
  subst this
  exact ProgE.isSample_map_liftSDistr f d

section Prog

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] [Countable PK] [Countable SK] [Countable SS]
  [Countable C] (O : KemOps PK SK SS C) (G : DHGroup S W)

omit [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The operations of `ltP` are uniform samples. -/
theorem ltP_allOps {E O' : Type} (s : RSt S W K) (pid : PartyId) :
    ProgE.AllOps ProgE.IsSample (ltP (E := E) (O := O') s pid) := by
  unfold ltP
  split
  · trivial
  · exact allOps_sample_liftSDistr fun _ => trivial

omit [Inhabited K] in
/-- The operations of `roP` are uniform samples. -/
theorem roP_allOps {E O' D : Type} [DecidableEq D] (tb : List (D × K)) (x : D) :
    ProgE.AllOps ProgE.IsSample (roP (E := E) (O := O') tb x) := by
  unfold roP
  split
  · trivial
  · exact allOps_sample_liftSDistr fun _ => trivial

omit [Field S] [Fintype S] [Countable PK] [Countable SK] [Countable SS] [Countable C] in
/-- The operations of `deliverP` are uniform samples. -/
theorem deliverP_allOps (s : PSt S W K PK SK SS C) (inp : Inst → Option (PInp W SS)) (x : Inst)
    (r : Rec K) (ip : PInp W SS) : ProgE.AllOps ProgE.IsSample (deliverP s inp x r ip) := by
  unfold deliverP
  split
  · exact ProgE.allOps_bind (roP_allOps _ _) fun _ => trivial
  · trivial

omit [Countable PK] [Countable SK] in
/-- The operations of `simCompleteP` are distribution samples. -/
theorem simCompleteP_allOps (s : SimSt S W K PK SK SS C) (x : Inst) :
    ProgE.AllOps ProgE.IsSample (simCompleteP O G s x) := by
  unfold simCompleteP
  split
  · split
    · split
      · exact ProgE.allOps_bind (ltP_allOps _ _) fun _ =>
          ProgE.allOps_bind (ltP_allOps _ _) fun _ =>
            allOps_sample (isSample_map_of_isPure (O.encaps_pureNF _).1 _) fun _ =>
              deliverP_allOps _ _ _ _ _
      · trivial
    · trivial
  · trivial

omit [Countable PK] [Countable SK] [Countable SS] [Countable C] in
/-- The operations of `simSendP` are uniform samples. -/
theorem simSendP_allOps (s : SimSt S W K PK SK SS C) (x : Inst) (e : W) (c : C) :
    ProgE.AllOps ProgE.IsSample (simSendP O G s x e c) := by
  unfold simSendP
  split
  · split
    · split
      · exact ProgE.allOps_bind (ltP_allOps _ _) fun _ =>
          ProgE.allOps_bind (ltP_allOps _ _) fun _ => deliverP_allOps _ _ _ _ _
      · trivial
    · trivial
  · trivial

/-- The operations of `simStartP` are distribution samples. -/
theorem simStartP_allOps (s : SimSt S W K PK SK SS C) (e : OEv W SS C) :
    ProgE.AllOps ProgE.IsSample (simStartP O G s e) := by
  rcases e with e | e <;> cases e <;> simp only [simStartP]
  all_goals try first
    | trivial
    | exact ProgE.allOps_bind (ltP_allOps _ _) fun _ => trivial
    | exact ProgE.allOps_bind (roP_allOps _ _) fun _ => trivial
    | exact simCompleteP_allOps O G _ _
    | exact simSendP_allOps O G _ _ _ _
  · split
    · refine allOps_sample_liftSDistr fun _ => ?_
      split
      · exact allOps_sample (isSample_map_of_isPure O.keygen_pureNF.1 _) fun _ => trivial
      · trivial
    · trivial
  · unfold simCorruptP
    split
    · trivial
    · exact ProgE.allOps_bind (ltP_allOps _ _) fun _ => trivial

omit [Field S] [Fintype S] [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] [Countable PK] [Countable SK] [Countable SS] [Countable C] in
/-- `simDecide` has no operation. -/
theorem simDecide_allOps (q : SimSt S W K PK SK SS C × Dec S W K PK C) :
    ProgE.AllOps ProgE.IsSample (simDecide q) := by
  unfold simDecide
  split
  · exact allOps_call fun _ => ProgE.allOps_bind allOps_outE fun _ => trivial
  · exact ProgE.allOps_bind allOps_outE fun _ => trivial

/-- **Every operation of the PQXDH simulator program is a distribution sample.** -/
theorem simBody_allOps (s : SimSt S W K PK SK SS C) :
    ProgE.AllOps ProgE.IsSample (simBody O G s) :=
  ProgE.allOps_bind allOps_recvO fun e =>
    ProgE.allOps_bind (simStartP_allOps O G s e) simDecide_allOps

/-- The costed PQXDH simulator program erases under the tree interpretation of samples to
`simBody O G`. -/
theorem simBodyT_eraseT (s : SimSt S W K PK SK SS C) :
    ProgE.eraseT ProgE.sampleTree (simBodyT O G s) = simBody O G s :=
  ProgE.eraseT_sampleTree_priced _ _ s (simBody_allOps O G s)

end Prog

derive_simulator pqxdhSimP

section Certificate

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] [Countable PK] [Countable SK] [Countable SS]
  [Countable C] (Pk : KEM.Games.Scheme PK SK SS C) (G : DHGroup S W)

/-- **Time certificate of the PQXDH program simulator.** The costed simulator on the costed
program `simBodyT (kemOps Pk) G` erases to `pqxdhSimP Pk G`, and its `j`-th activation costs at
most `17 + 2 j`: the key-derivation table grows by at most one entry per iteration, and a
lookup costs its length. -/
theorem pqxdhSimP_timeCertificate :
    (pqxdhSimP.timed Pk G _ ProgE.sampleTree (simBodyT (K := K) (kemOps Pk) G)).Erases
        (pqxdhSimP Pk G) ∧
      (pqxdhSimP.timed Pk G _ ProgE.sampleTree
        (simBodyT (K := K) (kemOps Pk) G)).TimeBoundGraded 17 2 :=
  ⟨pqxdhSimP.erase_timed Pk G _ _ _ (simBodyT_eraseT _ G),
    pqxdhSimP.timeBoundGraded_timed Pk G _ _ _
      (ProgE.LoopBoundGraded.sampleTree (simBodyT_loopBoundGraded _ G))⟩

end Certificate

end CatCrypt.Crypto.Party.Protocols.PQXDH
