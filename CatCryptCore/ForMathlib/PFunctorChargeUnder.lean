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
* `PFunctor.FreeM.wpFold_chargeUnder_liftBind_const_add` — a call charging `c a₁ + c a₂` folds
  as a call at `a₁` followed by a call at `a₂` (ticks merge)
* `PFunctor.FreeM.wpFold_chargeUnder_bind_le` — the bind clause: bounds on `x` and, at the returns
  of `x` satisfying a demonic invariant, on `f`, add to a bound on `x.bind f`
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

/-- A call at `a` whose continuation ignores the answer costs `c a` plus the continuation, when
`a` has an allowed answer. -/
theorem wpFold_chargeUnder_liftBind_const {R : Type w} [CompleteLattice R] [Add R]
    (c : P.A → R) (allows : (a : P.A) → P.B a → Prop) (a : P.A) {b : P.B a} (hb : allows a b)
    (y : FreeM P α) (post : α → R) :
    wpFold (OpSpec.chargeUnder c allows) (FreeM.liftBind a fun _ => y) post =
      c a + wpFold (OpSpec.chargeUnder c allows) y post := by
  rw [wpFold_liftBind, OpSpec.chargeUnder_apply]
  exact congrArg (c a + ·)
    (le_antisymm (iSup₂_le fun _ _ => le_rfl) (le_iSup₂_of_le b hb le_rfl))

/-- Ticks merge: a call at `a` with charge `c a₁ + c a₂` whose continuation ignores the answer
has the fold of a call at `a₁` followed by a call at `a₂`, when each has an allowed answer. -/
theorem wpFold_chargeUnder_liftBind_const_add {R : Type w} [CompleteLattice R] [AddSemigroup R]
    (c : P.A → R) (allows : (a : P.A) → P.B a → Prop) {a a₁ a₂ : P.A}
    (hc : c a = c a₁ + c a₂) {b : P.B a} (hb : allows a b) {b₁ : P.B a₁} (hb₁ : allows a₁ b₁)
    {b₂ : P.B a₂} (hb₂ : allows a₂ b₂) (y : FreeM P α) (post : α → R) :
    wpFold (OpSpec.chargeUnder c allows) (FreeM.liftBind a fun _ => y) post =
      wpFold (OpSpec.chargeUnder c allows)
        (FreeM.liftBind a₁ fun _ => FreeM.liftBind a₂ fun _ => y) post := by
  rw [wpFold_chargeUnder_liftBind_const c allows a hb,
    wpFold_chargeUnder_liftBind_const c allows a₁ hb₁,
    wpFold_chargeUnder_liftBind_const c allows a₂ hb₂, hc, add_assoc]

/-- A postcondition bounded by `k` at the returns satisfying `I`, where every allowed return of
`x` satisfies `I`, adds at most `k` to the charge fold of `x`. -/
theorem wpFold_chargeUnder_le_add_of_demonicUnder {X : Type*} (c : P.A → ℕ∞)
    (allows : (a : P.A) → P.B a → Prop) {x : FreeM P X} {post : X → ℕ∞} {I : X → Prop}
    {k : ℕ∞} (hI : wpFold (OpSpec.demonicUnder allows) x I) (hpost : ∀ a, I a → post a ≤ k) :
    wpFold (OpSpec.chargeUnder c allows) x post ≤
      wpFold (OpSpec.chargeUnder c allows) x (fun _ => 0) + k := by
  induction x with
  | pure a => simpa using hpost a hI
  | lift_bind a r ih =>
    change c a + (⨆ b, ⨆ (_ : allows a b), wpFold (OpSpec.chargeUnder c allows) (r b) post) ≤
      (c a + ⨆ b, ⨆ (_ : allows a b),
        wpFold (OpSpec.chargeUnder c allows) (r b) fun _ => 0) + k
    rw [add_assoc]
    exact add_le_add le_rfl (iSup₂_le fun b hb =>
      (ih b (hI b hb)).trans (add_le_add_left (le_iSup₂ (f := fun b (_ : allows a b) =>
        wpFold (OpSpec.chargeUnder c allows) (r b) fun _ => 0) b hb) k))

/-- The bind clause of the charge fold: bounds `m` on `x` and `n` on `f a` at every return `a`
satisfying `I`, where every allowed return of `x` satisfies `I`, bound `x.bind f` by `m + n`. -/
theorem wpFold_chargeUnder_bind_le {X Y : Type*} (c : P.A → ℕ∞)
    (allows : (a : P.A) → P.B a → Prop) {x : FreeM P X} {f : X → FreeM P Y} {I : X → Prop}
    {m n : ℕ∞} (hx : wpFold (OpSpec.chargeUnder c allows) x (fun _ => 0) ≤ m)
    (hf : ∀ a, I a → wpFold (OpSpec.chargeUnder c allows) (f a) (fun _ => 0) ≤ n)
    (hI : wpFold (OpSpec.demonicUnder allows) x I) :
    wpFold (OpSpec.chargeUnder c allows) (x.bind f) (fun _ => 0) ≤ m + n := by
  rw [wpFold_bind']
  exact (wpFold_chargeUnder_le_add_of_demonicUnder c allows hI hf).trans
    (add_le_add_left hx n)

/-- The demonic fold over the allowed answers is antitone in `allows`: a postcondition holding
at every return reachable under `allows` holds at every return reachable under fewer answers. -/
theorem wpFold_demonicUnder_of_le {X : Type*} {allows allows' : (a : P.A) → P.B a → Prop}
    (h : ∀ a b, allows' a b → allows a b) {x : FreeM P X} {Q : X → Prop}
    (hx : wpFold (OpSpec.demonicUnder allows) x Q) :
    wpFold (OpSpec.demonicUnder allows') x Q := by
  induction x with
  | pure a => exact hx
  | lift_bind a r ih => exact fun b hb => ih b (hx b (h a b hb))

/-- With every answer allowed, a bound on the charge fold is the subtractive roll bound. -/
theorem isRollBound_iff_wpFold_chargeUnder_true (c : P.A → ℕ) (x : FreeM P α) (n : ℕ) :
    IsRollBound x n (fun a b => c a ≤ b) (fun a b => b - c a) ↔
      wpFold (OpSpec.chargeUnder (fun a => (c a : ℕ∞)) fun _ _ => True) x (fun _ => 0) ≤
        n := by
  rw [OpSpec.chargeUnder_true, isRollBound_iff_wpFold_charge]

end FreeM

end PFunctor
