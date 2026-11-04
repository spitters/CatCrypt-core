/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Party.Protocols.IKNP
public import CatCryptCore.Crypto.Party.LoopTimed
public import CatCryptCore.Tactics.DeriveSimulator

/-!
# Running time of the IKNP program simulator

`derive_simulator` builds the costed form of the IKNP program simulator `simP`, the loop
`simLoop` of the simulator program `simBody`, on the costed loop `Prog.loopMulti.timed`. The
operations of `simBody` are the draws of the views of the corrupt sender (`simS a`) and of the
corrupt receiver (`simR a`). Given costed trees `simST a` and `simRT a` of these draws of time at
most `T`, the operations are interpreted by the family of the encoded trees `ProgE.encTree`
(`ProgE.treeBy`), under which the unit-cost form `simBodyT` of `simBody` erases to it. The
unit-weight bound `10` of an iteration then gives each activation the time bound `20 (T + 1)`.

No module imports this file.

## Main definitions

* `IKNPProg.iknpFamily`: the encoded costed trees of the two view completions.
* `IKNPProg.simBodyT`: the unit-cost form of the simulator program.

## Main results

* `simP.timed`, `simP.erase_timed`, `simP.timeBoundGraded_timed`: the costed form of the
  simulator by `derive_simulator`.
* `IKNPProg.simBodyT_eraseT`: the costed simulator program erases to `simBody`.
* `IKNPProg.simP_timeCertificate`: the costed simulator erases to `simP`, and each activation
  costs at most `20 (T + 1)`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Party.IKNPProg

open CatCrypt.Core CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.OT CatCrypt.Crypto.OT.IKNPWake

derive_simulator simP

variable {κ m : ℕ} {M P L : Type} [Zero M] {LS LR EGA OGA : Type} [Countable LS]
  [Countable LR]

/-- The family of the encoded costed trees of the view completions `simST` and `simRT`. -/
def iknpFamily (simST : OGA → ℕ × SPTree.Timed LS) (simRT : OGA → ℕ × SPTree.Timed LR)
    (x : ℕ × SPTree.Timed ℕ) : Prop :=
  (∃ a, x = ProgE.encTree (simST a)) ∨ ∃ a, x = ProgE.encTree (simRT a)

variable (ans : Option LS → Option LR → P → L) (sch : SchedEv → EGA)
  (stat : OGA → Bool × Bool) (pkEv : EGA) (simS : OGA → SPComp LS) (simR : OGA → SPComp LR)

/-- **The costed simulator program**: the unit-cost form of `simBody`, with no price. -/
noncomputable def simBodyT :
    SSt κ m M LS LR → ProgE (Costed (SPComp ℕ))
      (((InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P)) ⊕ (InOut m M ⊕ OGA))
      ((InEv m M ⊕ EGA) ⊕ (InOut m M ⊕ (AOut m M ⊕ L))) (SSt κ m M LS LR) :=
  ProgE.priced (fun _ => 0) (simBody ans sch stat pkEv simS simR)

variable {ans sch stat pkEv simS simR}
variable {simST : OGA → ℕ × SPTree.Timed LS} {simRT : OGA → ℕ × SPTree.Timed LR}

/-- A draw of the corrupt sender's view is an operation of the family. -/
theorem inFamily_simS (hS : ∀ a, (simST a).2.erase.compile = simS a) (a : OGA) :
    letI := Encodable.ofCountable LS
    ProgE.InFamily (iknpFamily simST simRT) (SPComp.map Encodable.encode (simS a)) :=
  ⟨ProgE.encTree (simST a), Or.inl ⟨a, rfl⟩, by rw [ProgE.encTree_compile, hS]⟩

/-- A draw of the corrupt receiver's view is an operation of the family. -/
theorem inFamily_simR (hR : ∀ a, (simRT a).2.erase.compile = simR a) (a : OGA) :
    letI := Encodable.ofCountable LR
    ProgE.InFamily (iknpFamily simST simRT) (SPComp.map Encodable.encode (simR a)) :=
  ⟨ProgE.encTree (simRT a), Or.inr ⟨a, rfl⟩, by rw [ProgE.encTree_compile, hR]⟩

omit [Zero M] [Countable LS] [Countable LR] in
/-- `sfin` has no operation. -/
theorem allOps_sfin {Q : SPComp ℕ → Prop} (s : SSt κ m M LS LR)
    (o : InOut m M ⊕ (AOut m M ⊕ L)) :
    ProgE.AllOps Q (sfin (P := P) (EGA := EGA) (OGA := OGA) s o) :=
  ProgE.allOps_bind Prog.allOps_outE fun _ => trivial

omit [Zero M] [Countable LS] [Countable LR] in
/-- `honK` has no operation. -/
theorem allOps_honK {Q : SPComp ℕ → Prop} (s : SSt κ m M LS LR) (o : InOut m M ⊕ OGA) :
    ProgE.AllOps Q (honK (P := P) (L := L) (EGA := EGA) s o) := by
  rcases o with o | o <;> exact allOps_sfin _ _

omit [Zero M] in
/-- The operations of `wR2K` are the draws of the receiver's view and those of the family. -/
theorem allOps_wR2K (hR : ∀ a, (simRT a).2.erase.compile = simR a) (s : SSt κ m M LS LR)
    (o : InOut m M ⊕ OGA) :
    ProgE.AllOps (fun q => ProgE.InFamily (iknpFamily simST simRT) q ∨ ProgE.IsSample q)
      (wR2K (P := P) (L := L) (EGA := EGA) simR s o) := by
  rcases o with o | a
  · exact Prog.allOps_call fun _ => allOps_honK _ _
  · exact Prog.allOps_sample (Or.inl (inFamily_simR hR a)) fun _ =>
      Prog.allOps_call fun _ => allOps_honK _ _

/-- The operations of `simBody` are draws of the view completions. -/
theorem simBody_allOps (hS : ∀ a, (simST a).2.erase.compile = simS a)
    (hR : ∀ a, (simRT a).2.erase.compile = simR a) (s : SSt κ m M LS LR) :
    ProgE.AllOps (fun q => ProgE.InFamily (iknpFamily simST simRT) q ∨ ProgE.IsSample q)
      (simBody ans sch stat pkEv simS simR s) := by
  refine ProgE.allOps_bind Prog.allOps_recvO fun e => ?_
  rcases e with (e | (i | _)) | ((⟨i, ev⟩ | d) | p)
  · exact Prog.allOps_call fun _ => allOps_honK _ _
  · simp only [simAct]
    split_ifs
    · refine Prog.allOps_call fun o => ?_
      rcases o with o | a
      · exact allOps_sfin _ _
      · exact Prog.allOps_sample (Or.inl (inFamily_simS hS a)) fun _ => allOps_sfin _ _
    · exact allOps_sfin _ _
    · exact allOps_sfin _ _
  · simp only [simAct]
    split
    · exact allOps_sfin _ _
    · refine Prog.allOps_call fun _ => ?_
      simp only [wR1K]
      split
      · exact Prog.allOps_call fun o => allOps_wR2K hR _ o
      · exact Prog.allOps_call fun _ => allOps_honK _ _
  · cases ev
    · exact allOps_sfin _ _
    · refine Prog.allOps_call fun o => ?_
      rcases o with o | a <;> exact allOps_sfin _ _
    · refine Prog.allOps_call fun o => ?_
      rcases o with o | a
      · exact allOps_sfin _ _
      · simp only [cdelK]
        split <;> exact allOps_sfin _ _
    · exact allOps_sfin _ _
  · exact allOps_sfin _ _
  · exact allOps_sfin _ _

/-- The costed simulator program erases to `simBody` under the interpretation by the encoded
trees of costed forms of the view completions. -/
theorem simBodyT_eraseT (hS : ∀ a, (simST a).2.erase.compile = simS a)
    (hR : ∀ a, (simRT a).2.erase.compile = simR a) (s : SSt κ m M LS LR) :
    ProgE.eraseT (ProgE.treeBy (iknpFamily simST simRT))
        (simBodyT ans sch stat pkEv simS simR s) =
      simBody ans sch stat pkEv simS simR s :=
  ProgE.eraseT_treeBy_priced _ _ _ s (simBody_allOps hS hR s)

/-- **Bound of the costed simulator program**: when each costed tree of the view completions
costs at most `T`, an iteration costs at most `10 (T + 1)`. -/
theorem simBodyT_loopBoundGraded {T : ℕ} (hST : ∀ a, SPTree.Timed.stepTime (simST a) ≤ T)
    (hRT : ∀ a, SPTree.Timed.stepTime (simRT a) ≤ T) :
    ProgE.LoopBoundGraded (ProgE.weightT (ProgE.treeBy (iknpFamily simST simRT)))
      (simBodyT ans sch stat pkEv simS simR) (SSt.init : SSt κ m M LS LR)
      (fun _ _ => True) ((T + 1) * (0 + 10)) ((T + 1) * 0) :=
  ProgE.LoopBoundGraded.treeBy
    (fun _ hx => by
      rcases hx with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · exact (ProgE.stepTime_encTree_le _).trans (hST a)
      · exact (ProgE.stepTime_encTree_le _).trans (hRT a))
    (ProgE.priced_loopBoundGraded (fun _ => 0) (simBody ans sch stat pkEv simS simR) SSt.init
      (fun _ _ => True) 10 0 0 trivial (fun _ _ _ => by omega)
      (fun _ s _ => simBody_bound ans sch stat pkEv simS simR s))

/-- **Time certificate of the IKNP program simulator.** Given costed trees `simST a` and
`simRT a` of the view completions of time at most `T`, the costed simulator on `simBodyT`
erases to `simP`, and each activation costs at most `20 (T + 1)`. -/
theorem simP_timeCertificate (hS : ∀ a, (simST a).2.erase.compile = simS a)
    (hR : ∀ a, (simRT a).2.erase.compile = simR a) {T : ℕ}
    (hST : ∀ a, SPTree.Timed.stepTime (simST a) ≤ T)
    (hRT : ∀ a, SPTree.Timed.stepTime (simRT a) ≤ T) :
    (simP.timed (κ := κ) (m := m) (M := M) ans sch stat pkEv simS simR _
        (ProgE.treeBy (iknpFamily simST simRT)) (simBodyT ans sch stat pkEv simS simR)).Erases
        (simP (κ := κ) (m := m) (M := M) ans sch stat pkEv simS simR) ∧
      (simP.timed (κ := κ) (m := m) (M := M) ans sch stat pkEv simS simR _
        (ProgE.treeBy (iknpFamily simST simRT))
        (simBodyT ans sch stat pkEv simS simR)).TimeBoundGraded (20 * (T + 1)) 0 := by
  refine ⟨simP.erase_timed ans sch stat pkEv simS simR _ _ _ (simBodyT_eraseT hS hR), ?_⟩
  refine (simP.timeBoundGraded_timed ans sch stat pkEv simS simR _ _ _
    (simBodyT_loopBoundGraded hST hRT)).mono ?_ ?_ <;> nlinarith

end CatCrypt.Crypto.Party.IKNPProg
