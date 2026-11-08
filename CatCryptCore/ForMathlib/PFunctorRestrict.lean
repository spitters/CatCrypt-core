/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.PFunctorChargeUnder
public import PolyFun.PFunctor.Free.Restrict

/-!
# Restricting the directions of a polynomial functor

PolyFun defines the restriction `PFunctor.restrict P allows` (the positions of `P` and, at a
position `a`, the directions `b` with `allows a b`), its inclusion `PFunctor.Lens.restrict`, the
transport of a tree along it `FreeM.restrict`, and folding along a lens as folding the pulled-back
specification (`FreeM.wpFold_mapLens`). For the restriction lens, the pullback of the charge
reading is the charge reading over the allowed answers, and the pullback of the demonic reading is
the demonic reading over the allowed answers.

## Main results

* `PFunctor.OpSpec.chargeUnder_eq` — `chargeUnder` is `charge` on the restriction, read through
  the inclusion of directions
* `PFunctor.FreeM.wpFold_chargeUnder_eq_restrict` — the charge fold over the allowed answers is
  the charge fold of the restricted tree
* `PFunctor.FreeM.wpFold_demonicUnder_iff_restrict` — the demonic fold over the allowed answers
  is the demonic fold of the restricted tree
-/

@[expose] public section

set_option autoImplicit false

universe uA uB v w

namespace PFunctor

namespace OpSpec

variable {P : PFunctor.{uA, uB}}

/-- `chargeUnder c allows` is the charge reading of the restriction, with the continuation read
through the inclusion of directions. -/
theorem chargeUnder_eq {R : Type w} [CompleteLattice R] [Add R] (c : P.A → R)
    (allows : (a : P.A) → P.B a → Prop) :
    chargeUnder c allows =
      fun a k => charge (P := P.restrict allows) c a (k ∘ Subtype.val) := by
  funext a k
  rw [chargeUnder_apply, iSup_subtype']
  rfl

/-- `demonicUnder allows` is the demonic reading of the restriction, with the continuation read
through the inclusion of directions. -/
theorem demonicUnder_eq (allows : (a : P.A) → P.B a → Prop) :
    demonicUnder allows = fun a k => demonic (P.restrict allows) a (k ∘ Subtype.val) := by
  funext a k
  exact propext ⟨fun h b => h b.1 b.2, fun h b hb => h ⟨b, hb⟩⟩

end OpSpec

namespace FreeM

variable {P : PFunctor.{uA, uB}} {α : Type v}

/-- The charge fold over the allowed answers is the charge fold of the restricted tree. -/
theorem wpFold_chargeUnder_eq_restrict {R : Type w} [CompleteLattice R] [Add R] (c : P.A → R)
    (allows : (a : P.A) → P.B a → Prop) (x : FreeM P α) (post : α → R) :
    wpFold (OpSpec.chargeUnder c allows) x post =
      wpFold (OpSpec.charge (P := P.restrict allows) c) (x.restrict allows) post := by
  rw [FreeM.restrict, wpFold_mapLens, OpSpec.chargeUnder_eq]
  rfl

/-- The demonic fold over the allowed answers is the demonic fold of the restricted tree. -/
theorem wpFold_demonicUnder_iff_restrict (allows : (a : P.A) → P.B a → Prop) (x : FreeM P α)
    (I : α → Prop) :
    wpFold (OpSpec.demonicUnder allows) x I ↔
      wpFold (OpSpec.demonic (P.restrict allows)) (x.restrict allows) I := by
  rw [FreeM.restrict, wpFold_mapLens, OpSpec.demonicUnder_eq]
  rfl

end FreeM

end PFunctor
