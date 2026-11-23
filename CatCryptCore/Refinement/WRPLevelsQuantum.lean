/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Refinement.WRPLevels
public import CatCryptCore.Refinement.RRelWRPQuantum

/-!
# Quantum channels as a level of refinement

The quantum computations of dimension `d` with one outcome, `QComp d Unit`, form a category
with one object: the identity is `pure ()` and composition is sequencing, `I >>= fun _ => J`.
Their weakest precondition at an observation, `ChannelWRP.instWPChannel`, is the observation
precomposed with the action of the computation on positive semidefinite matrices. It sends
`pure ()` to the identity transformer and a sequence to the composite transformer, so the
channels form a level `WRPLevels.CatLevel` with the lattice of observations
`PSDState d → ℝ≥0∞` and the trivial exception type `Unit`.

## Main definitions

* `ChanOb d`: the one object of the category of channels of dimension `d`.
* `instCategoryChanOb`: channels under sequencing.
* `channelLat d`: the lattice of observations.
* `channelTrans I`: the weakest precondition transformer of a channel.
* `channelLevel d`: the level of channels of dimension `d`; `channelFamily d`, the family with
  this one level.

## Main results

* `channelState_pure`, `channelState_seq`: the action of `pure ()` is the identity and the
  action of a sequence is the composite action.
* `channelTrans_id`, `channelTrans_comp`: the weakest precondition is strict.
* `sq_channelTrans_id_iff`, `sq_id_iff`: a square of channels along identity vertical arrows
  holds if and only if the channels are equal.
* `sq_id_channel`: every channel refines itself along the identity vertical arrows.
-/

@[expose] public section

set_option autoImplicit false

open Lean.Order CategoryTheory
open scoped ENNReal

noncomputable section

namespace CatCrypt.Refinement.WRPLevelsQuantum

open CatCrypt.Quantum ChannelWRP

variable {d : ℕ}

/-! ## The category of channels -/

/-- The action of `pure ()` on states is the identity. -/
theorem channelState_pure (ρ : PSDState d) : channelState (pure () : QComp d Unit) ρ = ρ := by
  apply Subtype.ext
  change (QComp.qpure () : QComp d Unit).branch () ρ.1 = ρ.1
  simp [QComp.qpure]

/-- The action of a sequence of channels is the composite action. -/
theorem channelState_seq (I J : QComp d Unit) (ρ : PSDState d) :
    channelState (I >>= fun _ => J) ρ = channelState J (channelState I ρ) := by
  apply Subtype.ext
  change ∑' a : Unit, J.branch () (I.branch a ρ.1) = J.branch () (I.branch () ρ.1)
  simp [tsum_fintype]

/-- The one object of the category of channels of dimension `d`. -/
inductive ChanOb (d : ℕ) : Type
  /-- The one object. -/
  | star

/-- Channels of dimension `d` under sequencing: the identity is `pure ()`, and `I ≫ J` runs
`I` and then `J`. -/
instance instCategoryChanOb : Category (ChanOb d) where
  Hom _ _ := QComp d Unit
  id _ := pure ()
  comp I J := I >>= fun _ => J
  id_comp I := by
    change (pure () >>= fun _ => I : QComp d Unit) = I
    simp
  comp_id I := by
    change (I >>= fun _ => pure () : QComp d Unit) = I
    simp
  assoc I J K := by
    change ((I >>= fun _ => J) >>= fun _ => K : QComp d Unit) = I >>= fun _ => J >>= fun _ => K
    simp

/-! ## The weakest precondition of a channel -/

/-- The lattice of observations of states of dimension `d`, with the trivial exception
type. -/
abbrev channelLat (d : ℕ) : WRPTransformers.Lat.{0, 0} where
  Pred := PSDState d → ℝ≥0∞
  E := Unit

/-- The weakest precondition transformer of a channel. -/
def channelTrans (I : QComp d Unit) : WRPTransformers.Trans (channelLat d) Unit Unit where
  tr Q E _ := Std.WP.wp I Q E
  mono _ h _ ρ := h () (channelState I ρ)

/-- The weakest precondition of `pure ()` is the identity transformer. -/
theorem channelTrans_id :
    channelTrans (pure () : QComp d Unit) = WRPTransformers.Trans.id Unit := by
  ext Q E x ρ
  change Q () (channelState (pure ()) ρ) = Q x ρ
  rw [channelState_pure]

/-- The weakest precondition of a sequence is the composite transformer. -/
theorem channelTrans_comp (I J : QComp d Unit) :
    channelTrans (I >>= fun _ => J) = (channelTrans I).comp (channelTrans J) := by
  ext Q E x ρ
  change Q () (channelState (I >>= fun _ => J) ρ) = Q () (channelState J (channelState I ρ))
  rw [channelState_seq]

/-- The object of predicate transformers of channels of dimension `d`. -/
abbrev channelObj (d : ℕ) : WRPTransformers.Obj.{0, 0, 0} := ⟨channelLat d, Unit⟩

/-- A square of channel transformers along identity vertical arrows holds if and only if the
two channels are equal. -/
theorem sq_channelTrans_id_iff (a c : QComp d Unit) :
    WRPTransformers.Sq (.mk (channelTrans a)) (WRPTransformers.VHom.id (channelObj d))
      (WRPTransformers.VHom.id (channelObj d)) (.mk (channelTrans c)) ↔ a = c := by
  rw [← channelRefines_iff, channelRefines_iff_le]
  refine ⟨fun h f ρ => ?_, fun h => ⟨rfl, rfl, fun Q E => ?_⟩⟩
  · have h3 := h.2.2 (fun _ => f) ()
    rw [WRPTransformers.VHom.conj_id, WRPTransformers.VHom.conj_id] at h3
    exact h3 () ρ
  · rw [WRPTransformers.VHom.conj_id, WRPTransformers.VHom.conj_id]
    exact fun _ ρ => h (Q ()) ρ

/-! ## The level of channels -/

/-- The channels of dimension `d` as a level: one object with the value type `Unit`, the
lattice of observations, and the weakest precondition `channelTrans`. -/
def channelLevel (d : ℕ) : WRPLevels.CatLevel.{0, 0, 0, 0, 0} where
  Ob := ChanOb d
  carrier _ := Unit
  lat := channelLat d
  wp I := channelTrans I
  wp_id _ := channelTrans_id
  wp_comp I J := channelTrans_comp I J

/-- The family with the one level of channels of dimension `d`. -/
abbrev channelFamily (d : ℕ) : Unit → WRPLevels.CatLevel.{0, 0, 0, 0, 0} :=
  fun _ => channelLevel d

/-- The object of the family of channels of dimension `d`. -/
abbrev chanObj (d : ℕ) : WRPLevels.Obj (channelFamily d) := ⟨(), (ChanOb.star : ChanOb d)⟩

/-- A refinement square between two channels along identity vertical arrows holds if and only
if the two channels are equal. -/
theorem sq_id_iff (a c : QComp d Unit) :
    WRPLevels.Sq (channelFamily d) (a := chanObj d) (b := chanObj d) (.mk a) (𝟙 (chanObj d))
      (𝟙 (chanObj d)) (.mk c) ↔ a = c :=
  sq_channelTrans_id_iff a c

/-- Every channel refines itself along the identity vertical arrows. -/
theorem sq_id_channel (a : QComp d Unit) :
    WRPLevels.Sq (channelFamily d) (a := chanObj d) (b := chanObj d) (.mk a) (𝟙 (chanObj d))
      (𝟙 (chanObj d)) (.mk a) :=
  (sq_id_iff a a).2 rfl

end CatCrypt.Refinement.WRPLevelsQuantum
