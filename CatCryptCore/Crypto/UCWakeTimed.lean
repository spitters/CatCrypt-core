/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCWake
public import CatCryptCore.Crypto.UCFeedbackTimed
public import CatCryptCore.Crypto.UCSimulatorCost
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveSimulator
public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.StdCosts

/-!
# Running time of the wake closure of a simulator

The costed form of the relabelling hybrid `wakeHybrid` of `UCWake.lean`, derived by
`derive_reduction`, with the time theorems of its steps (`derive_time_bound`) and of the hybrid
(`derive_hybrid_time`), the time theorem of the feedback hybrid `MultiHybrid.fbHybrid`, and the
costed form of the simulator `Simulator.wakeClose S` over a costed form `T` of `S`: the costed
feedback hybrid composed with the costed relabelling hybrid composed with `T`. With the costs of
the delivery map bounded by `t_dlv` and of the cut-off map by `t_cut`, its time is that of `T`
plus `t_cut + t_dlv + 6`. No module imports this file.

## Main results

* `wakeHybrid.timed`, `wakeHybrid.erase_timed`, `wakeHybrid.timeBound_timed`: the costed
  relabelling hybrid, its erasure and its time.
* `MultiHybrid.fbHybrid.timeBound_timed`: the time of the costed feedback hybrid.
* `Simulator.wakeClose.timed`, `Simulator.wakeClose.erase_timed`: the costed wake closure of a
  simulator and its erasure.
* `Simulator.wakeClose.timeBound_timed`: its time bound.
-/

@[expose] public section

set_option autoImplicit false

derive_reduction CatCrypt.Crypto.UCTransparent.wakeHybrid
derive_time_bound CatCrypt.Crypto.UCTransparent.wakeHybrid.start.tree
derive_time_bound CatCrypt.Crypto.UCTransparent.wakeHybrid.resume.tree
derive_time_bound CatCrypt.Crypto.UCTransparent.wakeHybrid.finish.tree
derive_hybrid_time CatCrypt.Crypto.UCTransparent.wakeHybrid
derive_hybrid_time CatCrypt.Crypto.UCTransparent.MultiHybrid.fbHybrid

namespace CatCrypt.Crypto.UCTransparent

variable {EH EA OH OA W EG OG : Type} {VH : PubView EH OH} {VA : PubView EA OA}
  {VG : PubView EG OG}

/-- The costed form of `Simulator.wakeClose` over a costed form `T` of the inner simulator, with
the costs `dlvCost` of the delivery map and `cutCost` of the cut-off map. -/
noncomputable def Simulator.wakeClose.timed (dlv : EA → Option W) (dlvCost : EA → ℕ)
    (cut : W → OH ⊕ OA) (cutCost : W → ℕ)
    (T : Simulator.Timed ((EH ⊕ W) ⊕ EA) (OH ⊕ OA) EG OG ((VH.wake W).sum VA) VG) :
    Simulator.Timed (EH ⊕ EA) (OH ⊕ OA) EG OG (VH.sum VA) VG :=
  .comp (U := (VH.sum VA).sum (PubView.ofProj _root_.id _root_.id))
    (.ofMultiHybrid (MultiHybrid.fbHybrid.timed 1 cut cutCost))
    (.comp (U := (VH.wake W).sum VA) (.ofMultiHybrid (wakeHybrid.timed dlv dlvCost)) T)

/-- **Erasure of the costed wake closure**: over a costed form of `S`, it erases to
`S.wakeClose dlv hdlv cut hcut`. -/
theorem Simulator.wakeClose.erase_timed
    {S : Simulator ((EH ⊕ W) ⊕ EA) (OH ⊕ OA) EG OG ((VH.wake W).sum VA) VG}
    {T : Simulator.Timed ((EH ⊕ W) ⊕ EA) (OH ⊕ OA) EG OG ((VH.wake W).sum VA) VG}
    (hT : T.Erases S) (dlv : EA → Option W) (dlvCost : EA → ℕ)
    (hdlv : ∀ a a', VA.ev a a' → dlv a = dlv a') (cut : W → OH ⊕ OA) (cutCost : W → ℕ)
    (hcut : ∀ w, (VH.sum VA).out (cut w) (cut w)) :
    (Simulator.wakeClose.timed dlv dlvCost cut cutCost T).Erases
      (S.wakeClose dlv hdlv cut hcut) :=
  Simulator.comp.erase_timed
    (Simulator.ofMultiHybrid.erase_timed (MultiHybrid.fbHybrid.erase_timed _ _ _) _)
    (Simulator.comp.erase_timed
      (Simulator.ofMultiHybrid.erase_timed (wakeHybrid.erase_timed _ _) _) hT)

/-- **Running time of the wake closure**: over a costed form of `S` with time `t`, with the
costs of the delivery map at most `t_dlv` and of the cut-off map at most `t_cut`, the costed
wake closure has time `t_cut + t_dlv + t + 6`. -/
theorem Simulator.wakeClose.timeBound_timed (dlv : EA → Option W) (dlvCost : EA → ℕ)
    (cut : W → OH ⊕ OA) (cutCost : W → ℕ)
    {T : Simulator.Timed ((EH ⊕ W) ⊕ EA) (OH ⊕ OA) EG OG ((VH.wake W).sum VA) VG}
    {t t_dlv t_cut : ℕ} (hT : T.TimeBound t) (hdlvC : ∀ a, dlvCost a ≤ t_dlv)
    (hcutC : ∀ w, cutCost w ≤ t_cut) :
    (Simulator.wakeClose.timed dlv dlvCost cut cutCost T).TimeBound (t_cut + t_dlv + t + 6) :=
  (Simulator.comp.timeBound_timed
    (Simulator.ofMultiHybrid.timeBound_timed
      (MultiHybrid.fbHybrid.timeBound_timed 1 cut cutCost hcutC))
    (Simulator.comp.timeBound_timed
      (Simulator.ofMultiHybrid.timeBound_timed (wakeHybrid.timeBound_timed dlv dlvCost hdlvC))
      hT)).mono (by omega)

end CatCrypt.Crypto.UCTransparent
