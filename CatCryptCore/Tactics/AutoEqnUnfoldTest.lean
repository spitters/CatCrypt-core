/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoEqnUnfold
public import CatCryptCore.Tactics.AutoArms

/-!
# Tests of `eqn_unfold`

Each test is over a definition of this module, and each positive test closes as the arm
would run in the dispatcher: `eqn_unfold; grind` or `eqn_unfold; simp_all`. The last
six tests have the shape of a front-recursive heap update by a list and an iterated
counter, with an induction hypothesis over all heaps; the last two close through
`catcrypt_auto`, whose `other` shape has the arm `eqn_unfold`.
-/

set_option autoImplicit false

namespace CatCrypt.Tactics.AutoEqnUnfoldTest

/-- The sum of a list, by structural recursion. -/
def lsum : List Nat → Nat
  | [] => 0
  | x :: xs => x + lsum xs

/-- Each element repeated twice, by structural recursion. -/
def dbl : List Nat → List Nat
  | [] => []
  | x :: xs => x :: x :: dbl xs

/-- The triangular numbers, by structural recursion on `Nat`. -/
def tri : Nat → Nat
  | 0 => 0
  | n + 1 => n + 1 + tri n

/-- The sum of a list in `Option`, by structural recursion. -/
def osum : List Nat → Option Nat
  | [] => some 0
  | x :: xs => (osum xs).bind fun s => some (x + s)

/-- The value of an option with default `0`, by `match` without recursion. -/
def getZ : Option Nat → Nat
  | none => 0
  | some n => n

/-- Half of a number, by well-founded recursion. -/
def half (n : Nat) : Nat :=
  if h : n < 2 then 0 else half (n - 2) + 1
termination_by n
decreasing_by omega

/-- Half of a number, by structural recursion with two base cases. -/
def half2 : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => half2 n + 1

example (x : Nat) (xs : List Nat) : x ≤ lsum (x :: xs) := by
  eqn_unfold; grind

example (x : Nat) (xs : List Nat) (h : lsum (x :: xs) = 0) : x = 0 := by
  eqn_unfold; grind

example (n : Nat) : n + 1 ≤ tri (n + 1) := by
  eqn_unfold; grind

example : tri 3 = 6 := by
  eqn_unfold; simp_all

example (x : Nat) (xs : List Nat) : lsum (dbl (x :: xs)) = 2 * x + lsum (dbl xs) := by
  eqn_unfold; grind

example (x : Nat) (xs : List Nat) (s : Nat) (h : osum xs = some s) :
    osum (x :: xs) = some (x + s) := by
  eqn_unfold; simp_all

example (n : Nat) : getZ (some n) = n := by
  eqn_unfold; grind

example (n : Nat) : half2 (n + 2) = half2 n + 1 := by
  eqn_unfold; grind

/-- error: eqn_unfold: no recursive definition applied to a constructor -/
#guard_msgs in
example (xs : List Nat) : 0 ≤ lsum xs := by
  eqn_unfold

/-- error: eqn_unfold: no recursive definition applied to a constructor -/
#guard_msgs in
example (n : Nat) : half n ≤ n := by
  eqn_unfold

/-- A heap of `W` values indexed by `Nat`. -/
structure H (W : Type) where
  /-- The cells. -/
  f : Nat → W

/-- Read a cell. -/
def H.get {W : Type} (σ : H W) (l : Nat) : W := σ.f l

/-- Write a cell. -/
def H.set {W : Type} (σ : H W) (l : Nat) (v : W) : H W :=
  ⟨fun k => if k = l then v else σ.f k⟩

/-- A read after a write of the same cell. -/
@[simp] theorem H.get_set_same {W : Type} (σ : H W) (l : Nat) (v : W) :
    (σ.set l v).get l = v := by simp [H.get, H.set]

/-- Two writes of the same cell. -/
@[simp] theorem H.set_set_same {W : Type} (σ : H W) (l : Nat) (v w : W) :
    (σ.set l v).set l w = σ.set l w := by
  simp only [H.set, H.mk.injEq]; funext k; split <;> rfl

/-- The counter cell written once for each element of the list. -/
def sh {W : Type} (nxt : W → W) : H W → List W → H W
  | σ, [] => σ
  | σ, _ :: ms => sh nxt (σ.set 0 (nxt (σ.get 0))) ms

/-- The counter advanced once for each element of the list. -/
def ic {W : Type} (nxt : W → W) : W → List W → W
  | n, [] => n
  | n, _ :: ms => ic nxt (nxt n) ms

example {W : Type} (nxt : W → W) (m : W) (ms : List W)
    (ih : ∀ σ : H W, (sh nxt σ ms).get 0 = ic nxt (σ.get 0) ms) (σ : H W) :
    (sh nxt σ (m :: ms)).get 0 = ic nxt (σ.get 0) (m :: ms) := by
  eqn_unfold; simp_all

example {W : Type} (nxt : W → W) (m : W) (ms : List W)
    (ih : ∀ σ : H W, (sh nxt σ ms).get 0 = ic nxt (σ.get 0) ms) (σ : H W) :
    (sh nxt σ (m :: ms)).get 0 = ic nxt (σ.get 0) (m :: ms) := by
  eqn_unfold; grind [H.get_set_same]

example {W : Type} (nxt : W → W) (m : W) (ms : List W)
    (ih : ∀ σ : H W, sh nxt σ ms = σ.set 0 (ic nxt (σ.get 0) ms)) (σ : H W) :
    sh nxt σ (m :: ms) = σ.set 0 (ic nxt (σ.get 0) (m :: ms)) := by
  eqn_unfold; simp_all

example {W : Type} (nxt : W → W) (m : W) (ms : List W)
    (ih : ∀ σ : H W, sh nxt σ ms = σ.set 0 (ic nxt (σ.get 0) ms)) (σ : H W) :
    sh nxt σ (m :: ms) = σ.set 0 (ic nxt (σ.get 0) (m :: ms)) := by
  eqn_unfold; grind [H.get_set_same, H.set_set_same]

example {W : Type} (nxt : W → W) (m : W) (ms : List W)
    (ih : ∀ σ : H W, (sh nxt σ ms).get 0 = ic nxt (σ.get 0) ms) (σ : H W) :
    (sh nxt σ (m :: ms)).get 0 = ic nxt (σ.get 0) (m :: ms) := by
  catcrypt_auto

example {W : Type} (nxt : W → W) (m : W) (ms : List W)
    (ih : ∀ σ : H W, sh nxt σ ms = σ.set 0 (ic nxt (σ.get 0) ms)) (σ : H W) :
    sh nxt σ (m :: ms) = σ.set 0 (ic nxt (σ.get 0) (m :: ms)) := by
  catcrypt_auto

end CatCrypt.Tactics.AutoEqnUnfoldTest
