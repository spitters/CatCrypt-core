/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.PFunctorChargeUnder

/-!
# Restricting the directions of a polynomial functor

`PFunctor.restrict P allows` is the sub-container of `P` with the same positions and, at a
position `a`, the directions `b` with `allows a b`. The inclusion of its directions is a lens
`PFunctor.Lens.restrict P allows : Lens P (P.restrict allows)` (positions fixed, directions
included), and `FreeM.restrict allows x` transports a tree along it: each node keeps its position
and its continuation is cut down to the admitted answers.

Folding a specification along a lens is folding its pullback along the lens (`wpFold_mapLens`).
For the restriction lens, the pullback of the charge reading is the charge reading over the
allowed answers, and the pullback of the demonic reading is the demonic reading over the allowed
answers.

## Main definitions

* `PFunctor.restrict` — the sub-container of the directions admitted by `allows`
* `PFunctor.Lens.restrict` — its inclusion, as a lens from `P`
* `PFunctor.FreeM.restrict` — a tree transported along the inclusion

## Main results

* `PFunctor.FreeM.wpFold_mapLens` — folding along a lens is folding the pulled-back
  specification
* `PFunctor.OpSpec.chargeUnder_eq` — `chargeUnder` is `charge` on the restriction, read through
  the inclusion of directions
* `PFunctor.FreeM.wpFold_chargeUnder_eq_restrict` — the charge fold over the allowed answers is
  the charge fold of the restricted tree
* `PFunctor.FreeM.wpFold_demonicUnder_iff_restrict` — the demonic fold over the allowed answers
  is the demonic fold of the restricted tree
-/

@[expose] public section

set_option autoImplicit false

universe uA uB uA₂ uB₂ v w

namespace PFunctor

/-- The sub-container of `P` with the directions admitted by `allows`: the positions of `P` and,
at a position `a`, the directions `b` with `allows a b`. -/
def restrict (P : PFunctor.{uA, uB}) (allows : (a : P.A) → P.B a → Prop) :
    PFunctor.{uA, uB} :=
  ⟨P.A, fun a => {b : P.B a // allows a b}⟩

/-- The inclusion of the restriction, as a lens from `P` to `P.restrict allows`: positions are
fixed and an admitted direction is sent to itself. -/
def Lens.restrict (P : PFunctor.{uA, uB}) (allows : (a : P.A) → P.B a → Prop) :
    Lens P (P.restrict allows) :=
  ⟨id, fun _ b => b.1⟩

namespace FreeM

variable {P : PFunctor.{uA, uB}} {α : Type v}

/-- A tree transported along the inclusion of the restriction: each node keeps its position and
its continuation is cut down to the answers admitted by `allows`. -/
protected def restrict (allows : (a : P.A) → P.B a → Prop) (x : FreeM P α) :
    FreeM (P.restrict allows) α :=
  x.mapLens (Lens.restrict P allows)

/-- Folding a specification along a lens is folding its pullback: a call at `a` is specified by
`Φ` at `l.toFunA a`, with the continuation read through `l.toFunB a`. -/
theorem wpFold_mapLens {Q : PFunctor.{uA₂, uB₂}} {l' : Type w} (l : Lens P Q) (Φ : OpSpec Q l')
    (x : FreeM P α) (post : α → l') :
    wpFold Φ (x.mapLens l) post = wpFold (fun a k => Φ (l.toFunA a) (k ∘ l.toFunB a)) x post := by
  induction x with
  | pure a => rfl
  | lift_bind a r ih =>
    change Φ (l.toFunA a) (fun d => wpFold Φ ((r (l.toFunB a d)).mapLens l) post) = _
    simp only [ih]
    rfl

end FreeM

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
