/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import PolyFun.PFunctor.Free.WP.Charge

/-!
# The charge reading restricted to allowed answers

`OpSpec.chargeUnder c allows` is the worst-case charge reading of `FreeM P` in which a call at
`a` costs `c a` and is followed by the worst continuation over the answers `b` with
`allows a b`, the answers a handler of the call can return. With `allows` true everywhere it is
`OpSpec.charge c`.

## Main definitions

* `PFunctor.OpSpec.chargeUnder` — the charge reading over the allowed answers

## Main results

* `PFunctor.OpSpec.chargeUnder_true` — with every answer allowed, `chargeUnder` is `charge`
* `PFunctor.FreeM.wpFold_chargeUnder_liftBind_le_iff` — a natural-number budget `n` bounds the
  charge fold of a call at `a` iff `c a ≤ n` and `n - c a` bounds the charge fold of the
  continuation at every allowed answer
* `PFunctor.FreeM.isRollBound_iff_wpFold_chargeUnder_true` — with every answer allowed, the
  bound is the subtractive roll bound
-/

@[expose] public section

set_option autoImplicit false

universe uA uB w

namespace PFunctor

namespace OpSpec

variable {P : PFunctor.{uA, uB}}

/-- The worst-case charge reading over the allowed answers: a call at `a` costs `c a`, followed
by the worst continuation at an answer `b` with `allows a b`. -/
noncomputable def chargeUnder {R : Type w} [CompleteLattice R] [Add R] (c : P.A → R)
    (allows : (a : P.A) → P.B a → Prop) : OpSpec P R :=
  fun a k => c a + ⨆ b, ⨆ (_ : allows a b), k b

@[simp]
theorem chargeUnder_apply {R : Type w} [CompleteLattice R] [Add R] (c : P.A → R)
    (allows : (a : P.A) → P.B a → Prop) (a : P.A) (k : P.B a → R) :
    chargeUnder c allows a k = c a + ⨆ b, ⨆ (_ : allows a b), k b :=
  rfl

/-- With every answer allowed, `chargeUnder` is `charge`. -/
theorem chargeUnder_true {R : Type w} [CompleteLattice R] [Add R] (c : P.A → R) :
    chargeUnder c (fun _ _ => True) = charge c := by
  funext a k
  simp

end OpSpec

namespace FreeM

variable {P : PFunctor.{uA, uB}} {α : Type uB}

/-- A natural-number budget `n` bounds the charge fold of a call at `a` iff `c a ≤ n` and
`n - c a` bounds the charge fold of the continuation at every allowed answer. -/
theorem wpFold_chargeUnder_liftBind_le_iff (c : P.A → ℕ) (allows : (a : P.A) → P.B a → Prop)
    (a : P.A) (r : P.B a → FreeM P α) (n : ℕ) :
    wpFold (OpSpec.chargeUnder (fun a => (c a : ℕ∞)) allows) (FreeM.liftBind a r)
        (fun _ => 0) ≤ n ↔
      c a ≤ n ∧ ∀ b, allows a b →
        wpFold (OpSpec.chargeUnder (fun a => (c a : ℕ∞)) allows) (r b) (fun _ => 0) ≤
          ((n - c a : ℕ) : ℕ∞) := by
  rw [wpFold_liftBind, OpSpec.chargeUnder_apply]
  constructor
  · intro h
    have hc : c a ≤ n := by exact_mod_cast le_self_add.trans h
    refine ⟨hc, fun b hb => ?_⟩
    have h' : (c a : ℕ∞) + wpFold (OpSpec.chargeUnder (fun a => (c a : ℕ∞)) allows) (r b)
        (fun _ => 0) ≤ (c a : ℕ∞) + ((n - c a : ℕ) : ℕ∞) := by
      rw [← Nat.cast_add, Nat.add_sub_cancel' hc]
      refine le_trans ?_ h
      gcongr
      exact le_iSup₂_of_le (f := fun b (_ : allows a b) =>
        wpFold (OpSpec.chargeUnder (fun a => (c a : ℕ∞)) allows) (r b) fun _ => 0) b hb le_rfl
    exact (ENat.add_le_add_iff_left (ENat.natCast_ne_top _)).1 h'
  · rintro ⟨hc, hr⟩
    calc _ ≤ (c a : ℕ∞) + ((n - c a : ℕ) : ℕ∞) := by gcongr; exact iSup₂_le hr
      _ = n := by rw [← Nat.cast_add, Nat.add_sub_cancel' hc]

/-- With every answer allowed, a bound on the charge fold is the subtractive roll bound. -/
theorem isRollBound_iff_wpFold_chargeUnder_true (c : P.A → ℕ) (x : FreeM P α) (n : ℕ) :
    IsRollBound x n (fun a b => c a ≤ b) (fun a b => b - c a) ↔
      wpFold (OpSpec.chargeUnder (fun a => (c a : ℕ∞)) fun _ _ => True) x (fun _ => 0) ≤
        n := by
  rw [OpSpec.chargeUnder_true, isRollBound_iff_wpFold_charge]

end FreeM

end PFunctor
