/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.X3DHSquareJoint
public import CatCryptCore.Crypto.AKE.X3DHSquareTimed
import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic
public import CatCryptCore.Tactics.DeriveSimulator
import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.DeriveTimeBound.Basic

/-!
# Running time of the X3DH simulator with the completion at a delivered prekey

`derive_reduction` builds the costed form `simProtC.timed` of the multi-call simulator
`simProtC` of `X3DHSquareJoint.lean` and its erasure theorem. On an event of the X3DH interface
the costed start step is the costed start step of `simProt` (`X3DHSquareTimed.lean`) delayed by
two units (`startC_inl_eq`), so its bound and its invariant are those of `simProt`. On a
completion `(x, spk)` (`simCompleteSig`) the step has the shape of the `complete` step of
`simProt`, with the delivered prekey `spk` in the key-derivation input; it reuses the bounds of
the two lookups of long-term secrets of `X3DHSquareTimed.lean` and has its own bound of the key
derivation (`kdfSig_time`).

After `i` activations a step costs at most `a + 40 i` on the invariant `SimInv`
(`simProtC.timeBoundGraded_timed`), and `derive_simulator` lifts the bound to `x3dhSimC`.

Only `X3DHSquareJointTimed.lean` imports this file.

## Main results

* `simProtC.timed`, `simProtC.erase_timed`: the costed multi-call simulator and its erasure.
* `simProtC.start.tree.timeBound_timed`: the time of `start`.
* `simProtC.timeBoundGraded_timed`: its graded time bound on the invariant `SimInv`.
* `x3dhSimC.timed`, `x3dhSimC.erase_timed`, `x3dhSimC.timeBoundGraded_timed`: the costed bundled
  simulator, its erasure, and its graded time bound.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.X3DHSquare

open CatCrypt.Core

set_option maxHeartbeats 400000 in
-- The start step reflects the ten event cases of `simStart` and the completion, with nested
-- record updates; the default of 200000 heartbeats does not suffice.
derive_reduction simProtC

derive_time_bound simProtC.resume.tree
derive_time_bound simProtC.finish.tree

section Time

open SPTree.Timed (stepTime_bind_bind_le stepTime_delay_bind_const_le)

variable {S W K : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K] [Nonempty K]
  [Inhabited K]

-- The costed steps of `simProtC` are compiled through the auxiliary matchers of its source, and
-- the bounds below unfold them by name.
set_option linter.auxLemma false

/-- On an event of the X3DH interface, the costed start step of `simProtC` is the costed start
step of `simProt` delayed by two units. -/
theorem startC_inl_eq (G : PAKE.DHExtract.DHGroup S W) (coe : S ≃ W → S → W)
    (coeCost : S ≃ W → S → ℕ) (expCost : W → S → ℕ) (toFunCost : S → ℕ)
    (s : SimSt S W K) (e : OEv W) :
    simProtC.start.tree.timed G coe coeCost s (.inl e) expCost toFunCost =
      SPTree.Timed.delay 2 (simProt.start.tree.timed G coe coeCost s e expCost toFunCost) := by
  have h13 : ∀ x coe coeCost e rc ec expCost toFunCost,
      simProtC.start.tree.match_13.timed (K := K) G x coe coeCost e rc ec expCost toFunCost =
        simProt.start.tree.match_13.timed G x e coe coeCost rc ec expCost toFunCost :=
    fun _ _ _ _ _ _ _ _ => rfl
  simp only [simProtC.start.tree.timed, simProtC.start.tree.match_19.timed,
    simProt.start.tree.timed, SPTree.Timed.delay, h13]
  grind

omit [Fintype S] [Inhabited K] in
/-- The key derivation at the input of the initiator with a delivered prekey costs at most
`12 + 3 t_toFun + 4 t_exp + 5 L` on a table of length `L`. -/
theorem kdfSig_time (G : PAKE.DHExtract.DHGroup S W) (p : UCTransparent.FAKE.Inst × W)
    (r : UCTransparent.FAKE.Rec K) (ek opk : S)
    (x y : (S × S) × RSt S W K) (toFunCost : S → ℕ) (expCost : W → S → ℕ) {te tf : ℕ}
    (he : ∀ a b, expCost a b ≤ te) (hf : ∀ a, toFunCost a ≤ tf) :
    SPTree.Timed.stepTime
        (simProtC.start.tree.match_16.timed G p r ek opk x y toFunCost expCost) ≤
      12 + 3 * tf + 4 * te + 5 * y.2.ro.length := by
  have hl := fun a => List.lookup.timedCost_le a y.2.ro
  simp only [simProtC.start.tree.match_16.timed, SPTree.Timed.stepTime]
  split <;> simp only [SPTree.Timed.time_ret, SPTree.Timed.time_sample] <;>
    grind [Finset.sup_eq_bot_iff, Nat.bot_eq_zero]

omit [Fintype S] [Inhabited K] in
/-- The key derivation at the input of the initiator with a delivered prekey adds at most one
entry to the table. -/
theorem kdfSig_allRet (G : PAKE.DHExtract.DHGroup S W) (p : UCTransparent.FAKE.Inst × W)
    (r : UCTransparent.FAKE.Rec K) (ek opk : S)
    (x y : (S × S) × RSt S W K) (toFunCost : S → ℕ) (expCost : W → S → ℕ) :
    SPTree.Timed.AllRet (fun z => z.2.length ≤ y.2.ro.length + 1)
      (simProtC.start.tree.match_16.timed G p r ek opk x y toFunCost expCost).2 := by
  simp only [simProtC.start.tree.match_16.timed]
  split
  · exact Nat.le_succ _
  · exact fun _ => le_rfl

/-- The completion step of the costed simulator (`simCompleteSig`), from a costed state whose
cost companions of the long-term secrets, of the inputs and of the corrupt parties vanish,
costs at most `60 + 3 t_coe + 3 t_toFun + 8 t_exp + 5 L` on a key-derivation table of length
`L`. -/
theorem completeSig_time (G : PAKE.DHExtract.DHGroup S W) (x : SimHat S W K)
    (coe : S ≃ W → S → W) (coeCost : S ≃ W → S → ℕ) (p : UCTransparent.FAKE.Inst × W)
    (expCost : W → S → ℕ) (toFunCost : S → ℕ)
    (hlt : x.1.2.1.2 = fun _ => 0) (hinp : x.2.1.2 = fun _ => 0)
    (hcor : x.1.1.2.1.2 = fun _ => 0) {tc te tf : ℕ}
    (hc : ∀ a b, coeCost a b ≤ tc) (he : ∀ a b, expCost a b ≤ te)
    (hf : ∀ a, toFunCost a ≤ tf) :
    SPTree.Timed.stepTime (simProtC.start.tree.match_18.timed G x coe coeCost p
        (fun _ => 0) (fun _ => 0) expCost toFunCost) ≤
      60 + 3 * tc + 3 * tf + 8 * te + 5 * x.1.2.2.2.length := by
  have h14 : ∀ (s : SimHat S W K) (p : UCTransparent.FAKE.Inst × W) c,
      simProtC.start.tree.match_14.timed s p c =
        simProt.start.tree.match_3.timed s p.1.1 p.1.2 c :=
    fun _ _ _ => rfl
  have h15 : ∀ (r : UCTransparent.FAKE.Rec K) (y : (S × S) × RSt S W K) (h : RHat S W K),
      simProtC.start.tree.match_15.timed r y h = simProt.start.tree.match_4.timed r y h :=
    fun _ _ _ => rfl
  simp only [simProtC.start.tree.match_18.timed]
  split
  · rename_i _ _ r ek _ _
    simp only [simProtC.start.tree.match_17.timed, h14, h15]
    rw [SPTree.Timed.stepTime_delay, SPTree.Timed.stepTime_delay,
      SPTree.Timed.stepTime_delay]
    rcases hO : opkOf (⟨⟨x.1.1.1.1, x.1.1.2.1.1, x.1.1.2.2.1, x.1.1.2.2.2⟩, x.1.2.1.1,
        x.1.2.2.1.1, x.1.2.2.2⟩ : RSt S W K) p.1.1 r.peer with _ | opk
    · simp only [SPTree.Timed.stepTime, SPTree.Timed.time_ret]
      split <;> (try split_ifs) <;> omega
    · simp only [SPTree.Timed.stepTime_delay]
      split_ifs
      · refine le_trans (Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_left
          (Nat.add_le_add_left (stepTime_bind_bind_le 1 1 _ _ _
            (lt1_time x p.1.1 p.1.2 (T := 0) fun p => by simp [hlt])
            (lt1_allRet x p.1.1 p.1.2 (T := 0) fun p => by simp [hlt])
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
                (kdfSig_time G p r ek opk _ _ toFunCost expCost he hf)) ?_
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
  · simp only [SPTree.Timed.stepTime, SPTree.Timed.delay, SPTree.Timed.time_ret]
    omega

/-- The completion step preserves the invariant, one activation later. -/
theorem completeSig_allRet (G : PAKE.DHExtract.DHGroup S W) (x : SimHat S W K)
    (coe : S ≃ W → S → W) (coeCost : S ≃ W → S → ℕ) (p : UCTransparent.FAKE.Inst × W)
    (rc ec : UCTransparent.FAKE.Inst → ℕ)
    (expCost : W → S → ℕ) (toFunCost : S → ℕ) (hlt : x.1.2.1.2 = fun _ => 0) {i : ℕ}
    (hx : HatInv i x) :
    SPTree.Timed.AllRet (fun y => HatInv (i + 1) y.1)
      (simProtC.start.tree.match_18.timed G x coe coeCost p rc ec expCost toFunCost).2 := by
  have h14 : ∀ (s : SimHat S W K) (p : UCTransparent.FAKE.Inst × W) c,
      simProtC.start.tree.match_14.timed s p c =
        simProt.start.tree.match_3.timed s p.1.1 p.1.2 c :=
    fun _ _ _ => rfl
  have h15 : ∀ (r : UCTransparent.FAKE.Rec K) (y : (S × S) × RSt S W K) (h : RHat S W K),
      simProtC.start.tree.match_15.timed r y h = simProt.start.tree.match_4.timed r y h :=
    fun _ _ _ => rfl
  obtain ⟨hro, hn⟩ := hx
  have hs : HatInv (i + 1) x := ⟨by omega, by omega⟩
  simp only [simProtC.start.tree.match_18.timed, SPTree.Timed.delay]
  split
  · rename_i _ _ r ek _ _
    simp only [simProtC.start.tree.match_17.timed, SPTree.Timed.delay, h14, h15]
    split
    · split_ifs
      · refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_mono (fun a ha => ?_) _
          (lt1_allRet x p.1.1 p.1.2 (T := 0) fun p => by simp [hlt]))
        refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_mono (fun b hb => ?_) _
          (lt2_allRet r _ a.2))
        dsimp only at hb
        split_ifs
        · refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_mono (fun z hz => ?_) _
            (kdfSig_allRet G p r ek _ _ _ toFunCost expCost))
          dsimp only at hz
          exact ⟨by dsimp only; grind, by dsimp only; grind⟩
        all_goals exact ⟨by dsimp only; grind, by dsimp only; grind⟩
      · exact hs
    · exact hs
  · exact hs

/-- The bound of the completion step on the costed tree of `start`. -/
theorem start_completeSig_time (G : PAKE.DHExtract.DHGroup S W) (coe : S ≃ W → S → W)
    (coeCost : S ≃ W → S → ℕ) (expCost : W → S → ℕ) (toFunCost : S → ℕ) (s : SimSt S W K)
    (p : UCTransparent.FAKE.Inst × W) {tc te tf : ℕ}
    (hc : ∀ a b, coeCost a b ≤ tc) (he : ∀ a b, expCost a b ≤ te)
    (hf : ∀ a, toFunCost a ≤ tf) :
    SPTree.Timed.stepTime (simProtC.start.tree.timed G coe coeCost s (.inr p)
        expCost toFunCost) ≤
      65 + 3 * tc + 3 * tf + 8 * te + 5 * s.1.ro.length := by
  simp only [simProtC.start.tree.timed]
  rw [SPTree.Timed.stepTime_delay]
  refine le_trans (SPTree.Timed.bind_ret_stepTime_le _ _) ?_
  simp only [SPTree.Timed.stepTime_delay, simProtC.start.tree.match_19.timed]
  have := completeSig_time G (coe := coe) (coeCost := coeCost) (p := p) (expCost := expCost)
    (toFunCost := toFunCost) (hlt := by rfl) (hinp := by rfl) (hcor := by rfl) hc he hf
    (x :=((((fun a ↦ s.1.st.recs a, fun _ ↦ 0), (fun a ↦ s.1.st.corrupt a, fun _ ↦ 0),
      s.1.st.notices, s.1.st.cursor), (fun a ↦ s.1.lt a, fun _ ↦ 0),
      (fun a ↦ s.1.eph a, fun _ ↦ 0), s.1.ro), (fun a ↦ s.2.1 a, fun _ ↦ 0), s.2.2))
  dsimp only at this ⊢
  omega

/-- **Time of the `start` step of the costed X3DH simulator with the completion at a delivered
prekey**: at most `202 + 20 t_coe + 20 t_exp + 20 t_toFun` plus twenty units per entry of the
key-derivation table and per notice of the state. -/
theorem simProtC.start.tree.timeBound_timed (G : PAKE.DHExtract.DHGroup S W)
    (coe : S ≃ W → S → W) (coeCost : S ≃ W → S → ℕ) (expCost : W → S → ℕ)
    (toFunCost : S → ℕ) (s : SimSt S W K) (e : CEv W) {tc te tf : ℕ}
    (hc : ∀ a b, coeCost a b ≤ tc) (he : ∀ a b, expCost a b ≤ te) (hf : ∀ a, toFunCost a ≤ tf) :
    SPTree.Timed.stepTime (simProtC.start.tree.timed G coe coeCost s e expCost toFunCost) ≤
      202 + 20 * tc + 20 * te + 20 * tf + 20 * s.1.ro.length +
        20 * s.1.st.notices.length := by
  rcases e with e | p
  · rw [startC_inl_eq, SPTree.Timed.stepTime_delay]
    have := simProt.start.tree.timeBound_timed G coe coeCost expCost toFunCost s e hc he hf
    omega
  · have := start_completeSig_time G coe coeCost expCost toFunCost s p hc he hf
    omega

/-- The `start` step of the simulator with the completion at a delivered prekey preserves the
invariant, one activation later. -/
theorem simProtC.start_allRet (G : PAKE.DHExtract.DHGroup S W) (coe : S ≃ W → S → W)
    (coeCost : S ≃ W → S → ℕ) (expCost : W → S → ℕ) (toFunCost : S → ℕ) (s : SimSt S W K)
    (e : CEv W) {i : ℕ} (hs : SimInv i s) :
    SPTree.Timed.AllRet (fun y => SimInv (i + 1) y.1)
      (simProtC.start.tree.timed G coe coeCost s e expCost toFunCost).2 := by
  rcases e with e | p
  · rw [startC_inl_eq]
    exact simProt.start_allRet G coe coeCost expCost toFunCost s e hs
  · obtain ⟨hro, hn⟩ := hs
    simp only [simProtC.start.tree.timed, SPTree.Timed.delay]
    refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_mono
      (Q := fun y : SimHat S W K × Dec S W K => HatInv (i + 1) y.1) (fun y hy => hy) _ ?_)
    simp only [simProtC.start.tree.match_19.timed, SPTree.Timed.delay]
    exact completeSig_allRet G _ coe coeCost p _ _ expCost toFunCost (by rfl)
      ⟨by dsimp only; omega, by dsimp only; omega⟩

/-- **Graded running time of the costed X3DH simulator with the completion at a delivered
prekey** on the invariant `SimInv`: after `i` activations every step costs at most `a + 40 i`,
with `a = 202 + 20 t_coe + 20 t_exp + 20 t_toFun`. -/
theorem simProtC.timeBoundGraded_timed (G : PAKE.DHExtract.DHGroup S W) (coe : S ≃ W → S → W)
    (coeCost : S ≃ W → S → ℕ) (expCost : W → S → ℕ) (toFunCost : S → ℕ) {tc te tf : ℕ}
    (hc : ∀ a b, coeCost a b ≤ tc) (he : ∀ a b, expCost a b ≤ te)
    (hf : ∀ a, toFunCost a ≤ tf) :
    (simProtC.timed (K := K) G coe coeCost expCost toFunCost).TimeBoundGraded SimInv
      (202 + 20 * tc + 20 * te + 20 * tf) 40 := by
  refine ⟨⟨by simp [simProtC.timed, rInit, UCTransparent.FAKE.initSt],
      by simp [simProtC.timed, rInit, UCTransparent.FAKE.initSt]⟩, fun i s e hs => ⟨?_,
      simProtC.start_allRet G coe coeCost expCost toFunCost s e hs⟩,
    fun i s o hs => ⟨?_, ?_⟩, fun i s o hs => ⟨?_, ?_⟩⟩
  · have := simProtC.start.tree.timeBound_timed G coe coeCost expCost toFunCost s e hc he hf
    obtain ⟨h1, h2⟩ := hs
    simp only [simProtC.timed, Prod.mk.eta]
    omega
  · have := simProtC.resume.tree.timeBound_timed G coe coeCost s o hc
    simp only [simProtC.timed, Prod.mk.eta]
    omega
  · obtain ⟨h1, h2⟩ := hs
    simp only [simProtC.timed, simProtC.resume.tree.timed]
    exact ⟨by dsimp only; omega, by dsimp only; omega⟩
  · have := simProtC.finish.tree.timeBound_timed G coe coeCost s o hc
    simp only [simProtC.timed, Prod.mk.eta]
    omega
  · obtain ⟨h1, h2⟩ := hs
    simp only [simProtC.timed, simProtC.finish.tree.timed]
    exact ⟨by dsimp only; omega, by dsimp only; omega⟩

end Time

derive_simulator x3dhSimC

end CatCrypt.Crypto.AKE.X3DHSquare
