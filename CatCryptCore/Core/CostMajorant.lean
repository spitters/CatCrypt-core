/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Order.Monotone.Basic
public import Mathlib.Order.Basic

/-!
# Majorants of cost companions

A cost companion `c : X → ℕ` of a time certificate is majorized by a monotone `M : ℕ → ℕ` along a
size `s : X → ℕ` when `c x ≤ M (s x)` at every argument (`CostMaj s M c`). This is Howard's
majorizability at the type `X → ℕ` of the monotone functional interpretation (Kohlenbach, *Applied
Proof Theory*, 2008, Ch. 6), with the arguments compared through their sizes; the bounded
functional interpretation of Ferreira and Oliva (APAL 2005) takes such majorants as the bounds of
its interpretation. A bound in a majorant is monotone in it, so that bounds compose without a case
analysis on the arguments: an argument of size at most `n` costs at most `M n` (`CostMaj.le`).

A uniform bound `∀ x, c x ≤ t`, the hypothesis that `derive_time_bound` states for a cost companion,
is majorizability by the constant `t` along any size (`costMaj_const_iff`). A majorant on the
arguments of size at most `N` (`CostMajOn`) gives the uniform bound `M N` there
(`CostMajOn.le_bound`).

## Main definitions

* `CostMaj`, `CostMajOn`

## Main results

* `CostMaj.le`, `costMaj_const_iff`, `CostMaj.add`, `CostMaj.mono_right`, `CostMaj.comp`,
  `CostMaj.costMajOn`, `CostMajOn.le_bound`

## References

* U. Kohlenbach, *Applied Proof Theory: Proof Interpretations and their Use in Mathematics*,
  Springer, 2008, Ch. 6 and 9;
* F. Ferreira, P. Oliva, *Bounded functional interpretation*, APAL 135 (2005).

Search words: majorant, majorizability, monotone functional interpretation, bounded functional
interpretation, cost companion, time bound, size.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Core

universe u v

variable {X : Type u} {Y : Type v}

/-- `M` majorizes the cost companion `c` along the size `s`: `M` is monotone and bounds `c` at every
argument at the value of `M` at its size. -/
def CostMaj (s : X → ℕ) (M : ℕ → ℕ) (c : X → ℕ) : Prop :=
  Monotone M ∧ ∀ x, c x ≤ M (s x)

/-- `M` majorizes `c` along `s` on the arguments of size at most `N`. -/
def CostMajOn (N : ℕ) (s : X → ℕ) (M : ℕ → ℕ) (c : X → ℕ) : Prop :=
  Monotone M ∧ ∀ x, s x ≤ N → c x ≤ M (s x)

namespace CostMaj

variable {s : X → ℕ} {M M' : ℕ → ℕ} {c c' : X → ℕ}

/-- An argument of size at most `n` costs at most `M n`. -/
theorem le (h : CostMaj s M c) {x : X} {n : ℕ} (hx : s x ≤ n) : c x ≤ M n :=
  (h.2 x).trans (h.1 hx)

/-- Majorants add. -/
theorem add (h : CostMaj s M c) (h' : CostMaj s M' c') :
    CostMaj s (fun n => M n + M' n) (fun x => c x + c' x) :=
  ⟨fun _ _ hab => Nat.add_le_add (h.1 hab) (h'.1 hab), fun x => Nat.add_le_add (h.2 x) (h'.2 x)⟩

/-- A larger monotone majorant is a majorant. -/
theorem mono_right (h : CostMaj s M c) (hM' : Monotone M') (hle : ∀ n, M n ≤ M' n) :
    CostMaj s M' c :=
  ⟨hM', fun x => (h.2 x).trans (hle _)⟩

/-- Precomposition by a map that does not increase the size. -/
theorem comp (h : CostMaj s M c) {t : Y → ℕ} {g : Y → X} (hg : ∀ y, s (g y) ≤ t y) :
    CostMaj t M (fun y => c (g y)) :=
  ⟨h.1, fun y => h.le (hg y)⟩

/-- A majorant is a majorant on the arguments of bounded size. -/
theorem costMajOn (h : CostMaj s M c) (N : ℕ) : CostMajOn N s M c :=
  ⟨h.1, fun x _ => h.2 x⟩

end CostMaj

/-- A uniform bound is majorizability by the constant along any size. -/
theorem costMaj_const_iff {s : X → ℕ} {c : X → ℕ} {t : ℕ} :
    CostMaj s (fun _ => t) c ↔ ∀ x, c x ≤ t :=
  ⟨fun h => h.2, fun h => ⟨fun _ _ _ => le_rfl, h⟩⟩

/-- On the arguments of size at most `N`, a majorant gives the uniform bound `M N`. -/
theorem CostMajOn.le_bound {N : ℕ} {s : X → ℕ} {M : ℕ → ℕ} {c : X → ℕ}
    (h : CostMajOn N s M c) {x : X} (hx : s x ≤ N) : c x ≤ M N :=
  (h.2 x hx).trans (h.1 hx)

end CatCrypt.Core
