/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Party.Protocols.X3DH
public import CatCryptCore.Crypto.Party.LoopTimed
public import CatCryptCore.Tactics.DeriveSimulator

/-!
# Running time of the X3DH program simulator

`derive_simulator` builds the costed form of the X3DH program simulator `x3dhSimP G`, the loop
`simLoop G` of the simulator program `simBody G`, on the costed loop `Prog.loopMulti.timed`. Its
costed body is the priced program `X3DHProg.simBodyT G` of `Party/Timed.lean`, which charges the
length of the key-derivation table per iteration. The operations of `simBody G` are uniform
samples (`simBody_allOps`), so under the tree interpretation of samples `ProgE.sampleTree` the
costed body erases to `simBody G`, and its graded bound `7`, `1` gives the simulator the graded
time bound `15`, `2`: the `j`-th activation costs at most `15 + 2 j`.

No module imports this file.

## Main results

* `x3dhSimP.timed`, `x3dhSimP.erase_timed`, `x3dhSimP.timeBoundGraded_timed`: the costed form
  of the simulator by `derive_simulator`.
* `X3DHProg.simBody_allOps`: every operation of the simulator program is a distribution sample.
* `x3dhSimP_timeCertificate`: the costed simulator erases to `x3dhSimP G`, and its `j`-th
  activation costs at most `15 + 2 j`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Party.X3DHProg

open CatCrypt.Core CatCrypt.Crypto.AKE.X3DHSquare CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract Prog

variable {S W K : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] (G : DHGroup S W)

omit [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The operations of `ltP` are uniform samples. -/
theorem ltP_allOps (s : RSt S W K) (pid : PartyId) :
    ProgE.AllOps ProgE.IsSample (ltP (S := S) (W := W) (K := K) s pid) := by
  unfold ltP
  split
  · trivial
  · exact allOps_sample_liftSDistr fun _ => trivial

omit [Field S] [Fintype S] [DecidableEq W] [Inhabited K] in
/-- The operations of `roP` are uniform samples. -/
theorem roP_allOps {D : Type} [DecidableEq D] (tb : List (D × K)) (x : D) :
    ProgE.AllOps ProgE.IsSample (roP (S := S) (W := W) tb x) := by
  unfold roP
  split
  · trivial
  · exact allOps_sample_liftSDistr fun _ => trivial

omit [Field S] [Fintype S] in
/-- The operations of `deliverP` are uniform samples. -/
theorem deliverP_allOps (rs : RSt S W K) (inp : Inst → Option (Inp W)) (x : Inst) (r : Rec K)
    (ip : Inp W) : ProgE.AllOps ProgE.IsSample (deliverP rs inp x r ip) := by
  unfold deliverP
  split
  · exact ProgE.allOps_bind (roP_allOps _ _) fun _ => trivial
  · trivial

/-- The operations of `simCompleteP` are uniform samples. -/
theorem simCompleteP_allOps (s : SimSt S W K) (x : Inst) :
    ProgE.AllOps ProgE.IsSample (simCompleteP G s x) := by
  unfold simCompleteP
  split
  · split
    · split
      · exact ProgE.allOps_bind (ltP_allOps _ _) fun _ =>
          ProgE.allOps_bind (ltP_allOps _ _) fun _ => deliverP_allOps _ _ _ _ _
      · trivial
    · trivial
  · trivial

/-- The operations of `simSendP` are uniform samples. -/
theorem simSendP_allOps (s : SimSt S W K) (x : Inst) (e : W) :
    ProgE.AllOps ProgE.IsSample (simSendP G s x e) := by
  unfold simSendP
  split
  · split
    · exact ProgE.allOps_bind (ltP_allOps _ _) fun _ =>
        ProgE.allOps_bind (ltP_allOps _ _) fun _ => deliverP_allOps _ _ _ _ _
    · trivial
  · trivial

/-- The operations of `simStartP` are uniform samples. -/
theorem simStartP_allOps (s : SimSt S W K) (e : OEv W) :
    ProgE.AllOps ProgE.IsSample (simStartP G s e) := by
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) |
    (_ | _ | pid | ⟨sid, pid⟩ | pid | ⟨sid, pid⟩ | ⟨sid, pid, w⟩ | x)
  · simp only [simStartP]
    split
    · exact allOps_sample_liftSDistr fun _ => trivial
    · trivial
  · trivial
  · trivial
  · trivial
  · exact ProgE.allOps_bind (ltP_allOps _ _) fun _ => trivial
  · trivial
  · simp only [simStartP, simCorruptP]
    split
    · trivial
    · exact ProgE.allOps_bind (ltP_allOps _ _) fun _ => trivial
  · exact simCompleteP_allOps G s (sid, pid)
  · exact simSendP_allOps G s (sid, pid) w
  · exact ProgE.allOps_bind (roP_allOps _ _) fun _ => trivial

omit [Field S] [Fintype S] [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- `simDecide` has no operation. -/
theorem simDecide_allOps (q : SimSt S W K × Dec S W K) :
    ProgE.AllOps ProgE.IsSample (simDecide q) := by
  unfold simDecide
  split
  · exact allOps_call fun _ => ProgE.allOps_bind allOps_outE fun _ => trivial
  · exact ProgE.allOps_bind allOps_outE fun _ => trivial

/-- **Every operation of the X3DH simulator program is a distribution sample.** -/
theorem simBody_allOps (s : SimSt S W K) : ProgE.AllOps ProgE.IsSample (simBody G s) :=
  ProgE.allOps_bind allOps_recvO fun e =>
    ProgE.allOps_bind (simStartP_allOps G s e) simDecide_allOps

/-- The costed X3DH simulator program erases under the tree interpretation of samples to
`simBody G`. -/
theorem simBodyT_eraseT (s : SimSt S W K) :
    ProgE.eraseT ProgE.sampleTree (simBodyT G s) = simBody G s :=
  ProgE.eraseT_sampleTree_priced _ _ s (simBody_allOps G s)

end CatCrypt.Crypto.Party.X3DHProg

namespace CatCrypt.Crypto.Party.Protocols.X3DH

open CatCrypt.Core CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.Party.X3DHProg

derive_simulator x3dhSimP

end CatCrypt.Crypto.Party.Protocols.X3DH
