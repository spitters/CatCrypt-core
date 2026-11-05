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
* `PFunctor.FreeM.wpFold_chargeUnder_pure_le`, `PFunctor.FreeM.wpFold_chargeUnder_liftBind_le`,
  `PFunctor.FreeM.wpFold_chargeUnder_bind_le_add`, `PFunctor.FreeM.wpFold_ite_le_max_enat`,
  `PFunctor.FreeM.wpFold_dite_le_max_enat` — the clauses of the fold rule of
  `derive_time_bound`, each bound a natural number cast to `ℕ∞`
* `PFunctor.FreeM.wpFold_demonicUnder_true` — the trivial leaf invariant
-/

@[expose] public section

set_option autoImplicit false

universe uA uB w uX uY

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

/-! ## The clauses of the fold rule

Each clause bounds the charge fold of a program by a natural number cast to `ℕ∞` from the
bounds of its parts, so that a bound computed clause by clause is a term of `ℕ`. -/

section Rule

variable {X Y : Type uX}

/-- The cast of naturals into `ℕ∞` is monotone. -/
theorem enat_natCast_le {m n : ℕ} (h : m ≤ n) : (m : ℕ∞) ≤ (n : ℕ∞) := by
  exact_mod_cast h

/-- A return charges nothing. -/
theorem wpFold_chargeUnder_pure_le (c : P.A → ℕ) (allows : (a : P.A) → P.B a → Prop) (x : X)
    (n : ℕ) :
    wpFold (OpSpec.chargeUnder (fun a => (c a : ℕ∞)) allows) (FreeM.pure x : FreeM P X)
      (fun _ => 0) ≤ (n : ℕ∞) :=
  zero_le

/-- A call at `a` is bounded by a bound `m` of its charge plus a bound `n` of its continuation at
every allowed answer. -/
theorem wpFold_chargeUnder_liftBind_le (c : P.A → ℕ) (allows : (a : P.A) → P.B a → Prop)
    (a : P.A) (r : P.B a → FreeM P X) (m n : ℕ) (hc : c a ≤ m)
    (hr : ∀ b, allows a b →
      wpFold (OpSpec.chargeUnder (fun a => (c a : ℕ∞)) allows) (r b) (fun _ => 0) ≤ (n : ℕ∞)) :
    wpFold (OpSpec.chargeUnder (fun a => (c a : ℕ∞)) allows) (FreeM.liftBind a r)
      (fun _ => 0) ≤ ((m + n : ℕ) : ℕ∞) := by
  rw [wpFold_liftBind, OpSpec.chargeUnder_apply, Nat.cast_add]
  exact add_le_add (by exact_mod_cast hc) (iSup₂_le hr)

/-- The bind clause with natural-number bounds: a bound `m` of `x` and a bound `n` of `f a` at
every return `a` satisfying the leaf invariant `I` of `x` add to a bound of `x.bind f`. -/
theorem wpFold_chargeUnder_bind_le_add (c : P.A → ℕ) (allows : (a : P.A) → P.B a → Prop)
    (x : FreeM P X) (f : X → FreeM P Y) (I : X → Prop) (m n : ℕ)
    (hx : wpFold (OpSpec.chargeUnder (fun a => (c a : ℕ∞)) allows) x (fun _ => 0) ≤ (m : ℕ∞))
    (hf : ∀ a, I a →
      wpFold (OpSpec.chargeUnder (fun a => (c a : ℕ∞)) allows) (f a) (fun _ => 0) ≤ (n : ℕ∞))
    (hI : wpFold (OpSpec.demonicUnder allows) x I) :
    wpFold (OpSpec.chargeUnder (fun a => (c a : ℕ∞)) allows) (x.bind f) (fun _ => 0) ≤
      ((m + n : ℕ) : ℕ∞) := by
  rw [Nat.cast_add]
  exact wpFold_chargeUnder_bind_le _ allows hx hf hI

/-- Every return satisfies the trivial invariant. -/
theorem wpFold_demonicUnder_true (allows : (a : P.A) → P.B a → Prop) (x : FreeM P X) :
    wpFold (OpSpec.demonicUnder allows) x (fun _ => True) := by
  induction x with
  | pure a => trivial
  | lift_bind a r ih => exact fun b _ => ih b

/-- A call whose continuation ignores the answer keeps the leaf invariant of the continuation. -/
theorem wpFold_demonicUnder_liftBind_const (allows : (a : P.A) → P.B a → Prop) (a : P.A)
    {y : FreeM P X} {I : X → Prop} (h : wpFold (OpSpec.demonicUnder allows) y I) :
    wpFold (OpSpec.demonicUnder allows) (FreeM.liftBind a fun _ => y) I :=
  fun _ _ => h

/-- An `if` of programs is bounded in `ℕ∞` by the maximum of the bounds of its branches. -/
theorem wpFold_ite_le_max_enat (Φ : OpSpec P ℕ∞) (p : Prop) [Decidable p] (x y : FreeM P X)
    (post : X → ℕ∞) {m n : ℕ} (hx : wpFold Φ x post ≤ (m : ℕ∞)) (hy : wpFold Φ y post ≤ (n : ℕ∞)) :
    wpFold Φ (if p then x else y) post ≤ ((max m n : ℕ) : ℕ∞) := by
  split
  · exact hx.trans (enat_natCast_le (le_max_left m n))
  · exact hy.trans (enat_natCast_le (le_max_right m n))

/-- A dependent `if` of programs is bounded in `ℕ∞` by the maximum of the bounds of its
branches. -/
theorem wpFold_dite_le_max_enat (Φ : OpSpec P ℕ∞) (p : Prop) [Decidable p] (x : p → FreeM P X)
    (y : ¬p → FreeM P X) (post : X → ℕ∞) {m n : ℕ} (hx : ∀ h, wpFold Φ (x h) post ≤ (m : ℕ∞))
    (hy : ∀ h, wpFold Φ (y h) post ≤ (n : ℕ∞)) :
    wpFold Φ (if h : p then x h else y h) post ≤ ((max m n : ℕ) : ℕ∞) := by
  split
  · exact (hx _).trans (enat_natCast_le (le_max_left m n))
  · exact (hy _).trans (enat_natCast_le (le_max_right m n))

/-- A natural number below a fold bounded by `m` is at most `m`. -/
theorem natCast_le_of_le_trans {a m : ℕ} {w' : ℕ∞} (h₁ : (a : ℕ∞) ≤ w') (h₂ : w' ≤ (m : ℕ∞)) :
    a ≤ m := by
  exact_mod_cast h₁.trans h₂

/-- A summand of a fold bounded by `n` is bounded by `n`: `s = d + w` and `s ≤ n` give `w ≤ n`
(the charge fold of the tree of a step-prefixed tree is at most the charge fold of the step-prefixed
tree). -/
theorem enat_le_of_add_eq {s w' : ℕ∞} {d n : ℕ} (hs : s = (d : ℕ∞) + w') (h : s ≤ (n : ℕ∞)) :
    w' ≤ (n : ℕ∞) :=
  le_trans (by rw [hs]; exact le_add_self) h

/-- The arithmetic of a step: `X = ca + w` with `ca ≤ m` and `w ≤ n` gives `X ≤ m + n`. -/
theorem enat_eq_add_le {X' w' : ℕ∞} {ca m n : ℕ} (hX : X' = (ca : ℕ∞) + w') (hc : ca ≤ m)
    (hn : w' ≤ (n : ℕ∞)) : X' ≤ ((m + n : ℕ) : ℕ∞) := by
  rw [hX, Nat.cast_add]
  exact add_le_add (enat_natCast_le hc) hn

/-- A bound `m ≤ n` weakens a bound of a fold. -/
theorem wpFold_le_natCast_of_le {w' : ℕ∞} {m n : ℕ} (h : w' ≤ (m : ℕ∞))
    (hmn : m ≤ n) : w' ≤ (n : ℕ∞) :=
  h.trans (enat_natCast_le hmn)

/-- The arithmetic of a split tick: `X = ca + w` and `s = d + w` with `ca = e + d`, `e ≤ m` and
`s ≤ n` give `X ≤ m + n`. -/
theorem enat_split_le {X' s w' : ℕ∞} {ca e d m n : ℕ} (hX : X' = (ca : ℕ∞) + w')
    (hs : s = (d : ℕ∞) + w') (hc : ca = e + d) (he : e ≤ m) (hn : s ≤ (n : ℕ∞)) :
    X' ≤ ((m + n : ℕ) : ℕ∞) := by
  rw [hX, hc, Nat.cast_add, add_assoc, ← hs, Nat.cast_add]
  exact add_le_add (enat_natCast_le he) hn

/-- The arithmetic of a tick split twice: `X = ca + w`, `s = d + w`, `s = u`, `v = d' + u`
with `ca = e + d' + d`, `e ≤ m` and `v ≤ n` give `X ≤ m + n`. -/
theorem enat_split₂_le {X' s w' u v : ℕ∞} {ca e d d' m n : ℕ} (hX : X' = (ca : ℕ∞) + w')
    (hs : s = (d : ℕ∞) + w') (hsu : s = u) (hv : v = (d' : ℕ∞) + u) (hc : ca = e + d' + d)
    (he : e ≤ m) (hn : v ≤ (n : ℕ∞)) : X' ≤ ((m + n : ℕ) : ℕ∞) := by
  rw [hX, hc, Nat.cast_add, Nat.cast_add, add_assoc, add_assoc, ← hs, hsu, ← hv, Nat.cast_add]
  exact add_le_add (enat_natCast_le he) hn

/-- The worst-case charge fold is the charge fold with every answer allowed. -/
theorem wpFold_charge_eq_chargeUnder_true {R : Type w} [CompleteLattice R] [Add R]
    (c : P.A → R) (x : FreeM P X) (post : X → R) :
    wpFold (OpSpec.charge c) x post = wpFold (OpSpec.chargeUnder c fun _ _ => True) x post := by
  rw [OpSpec.chargeUnder_true]

end Rule

end FreeM

end PFunctor
