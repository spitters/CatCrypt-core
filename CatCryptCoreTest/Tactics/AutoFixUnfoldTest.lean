/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoArms
public import CatCryptCore.Tactics.AutoBase
public import CatCryptCore.Core.Code
public import CatCryptCore.Crypto.UCAdmClass

/-!
# Tests of `hyp_unfold`, `funext_unfold`, dominance lemmas in `hop_chain`, and the
Boolean-split arm without a split

Each procedure is tested over fresh definitions, called directly and through
`catcrypt_auto`. The program type of the `funext_unfold` tests is private to this module
and registered by its short name.
-/

set_option autoImplicit false

open CatCrypt.Core CatCrypt.Prob
open scoped ENNReal

namespace CatCrypt.Tactics.AutoFixUnfoldTest

/-! ## `hyp_unfold` -/

/-- A predicate on numbers. -/
def BadFresh (n : ℕ) : Prop := n = 3 ∨ n = 5

/-- A predicate defined through another one. -/
def GoodFresh (n : ℕ) : Prop := 2 ≤ n ∧ n ≤ 4

/-- A predicate whose unfolding exposes `GoodFresh`. -/
def OkFresh (n : ℕ) : Prop := GoodFresh n ∧ n ≠ 3

example (x : ℕ) (hx : x = 3) (hnot : ¬ BadFresh x) : False := by
  hyp_unfold
  grind

example (n : ℕ) (h : OkFresh n) : n = 2 ∨ n = 4 := by
  hyp_unfold
  omega

example (x : ℕ) (hx : x = 5) (hnot : ¬ BadFresh x) : False := by
  catcrypt_auto

example (x : ℕ) (hx : x = 5) : x + 0 = 5 := by
  fail_if_success hyp_unfold
  grind

/-! ## `funext_unfold` -/

/-- A program type over a state of numbers, private to this module. -/
def ProgFresh (α : Type) := ℕ → Option (α × ℕ)

catcrypt_funext_type ProgFresh

/-- Return of `ProgFresh`. -/
def ProgFresh.ret {α : Type} (a : α) : ProgFresh α := fun s => some (a, s)

/-- Sequencing of `ProgFresh`. -/
def ProgFresh.seq {α β : Type} (c : ProgFresh α) (f : α → ProgFresh β) : ProgFresh β :=
  fun s => (c s).bind fun p => f p.1 p.2

example {α β : Type} (a : α) (f : α → ProgFresh β) :
    ProgFresh.seq (ProgFresh.ret a) f = f a := by
  funext_unfold
  rfl

example {α : Type} (c : ProgFresh α) : ProgFresh.seq c ProgFresh.ret = c := by
  funext_unfold
  simp

/-- A lift of a distribution to a computation that leaves the heap unchanged. -/
noncomputable def liftFresh {α : Type} (d : SDistr α) : SPComp α :=
  fun h => SDistr.bind d (fun a => SDistr.pure (a, h))

example {α : Type} (a : α) : liftFresh (SDistr.pure a) = SPComp.pure a := by
  funext_unfold
  simp [SDistr.pure_bind]

example {α : Type} :
    (fun a : α => liftFresh (SDistr.pure a)) = fun a => SPComp.pure a := by
  funext_unfold
  simp [SDistr.pure_bind]

example {α β : Type} (d : SDistr α) (f : α → SDistr β) :
    liftFresh (SDistr.bind d f) = SPComp.bind (liftFresh d) (fun a => liftFresh (f a)) := by
  catcrypt_auto

example (a b : ℕ) (h : a = b) : a + 1 = b + 1 := by
  fail_if_success funext_unfold
  grind

/-! ## Dominance lemmas in `hop_chain` -/

/-- A pseudometric `d₁` dominated by a function `d₂`. -/
structure DPM (X : Type) where
  /-- The dominated distance. -/
  d₁ : X → X → ℝ≥0∞
  /-- The dominating distance. -/
  d₂ : X → X → ℝ≥0∞
  /-- Triangle inequality of `d₁`. -/
  tri : ∀ x y z, d₁ x z ≤ d₁ x y + d₁ y z
  /-- Dominance. -/
  dom : ∀ x y, d₁ x y ≤ d₂ x y

/-- The triangle inequality of `DPM.d₁`. -/
@[hop_metric] theorem DPM.d₁_triangle {X : Type} (M : DPM X) (x y z : X) :
    M.d₁ x z ≤ M.d₁ x y + M.d₁ y z := M.tri x y z

/-- The dominance of `DPM.d₁` by `DPM.d₂`. -/
@[hop_metric] theorem DPM.d₁_le_d₂ {X : Type} (M : DPM X) (x y : X) :
    M.d₁ x y ≤ M.d₂ x y := M.dom x y

example {X : Type} (M : DPM X) (a b c : X) (e₁ e₂ : ℝ≥0∞) (h₁ : M.d₂ a b ≤ e₁)
    (h₂ : M.d₁ b c ≤ e₂) : M.d₁ a c ≤ e₁ + e₂ := by
  hop_chain

example {X : Type} (M : DPM X) (a b : X) (e f : ℝ≥0∞) (h : M.d₂ a b ≤ e) (hef : e ≤ f) :
    M.d₁ a b ≤ f := by
  hop_chain

example {T : Type → Type} [UCMonad.UCMonadCompDist T] {α β : Type} (f g h : α → T β)
    (e₁ e₂ : ℝ≥0∞) (h₁ : UCMonad.UCMonadMetric.ucSdist f g ≤ e₁)
    (h₂ : UCMonad.ucCdist g h ≤ e₂) : UCMonad.ucCdist f h ≤ e₁ + e₂ := by
  hop_chain

example {T : Type → Type} [UCMonad.UCMonadCompDist T] {α β : Type} (f g : α → T β)
    (e : ℝ≥0∞) (h₁ : UCMonad.UCMonadMetric.ucSdist f g ≤ e) :
    UCMonad.ucCdist f g ≤ e := by
  catcrypt_auto

example (x y : ℝ≥0∞) (h : x ≤ y) : x ≤ y + 0 := by
  fail_if_success hop_chain
  simpa using h

/-! ## The Boolean-split arm of `SPComp equality` without a split -/

/-- A computation read from a table of computations, with a default. -/
public noncomputable def lookupFresh (tbl : ℕ → Option (SPComp ℕ)) (dflt : SPComp ℕ) (k : ℕ) :
    SPComp ℕ :=
  (tbl k).getD dflt

/-- The goal has no Boolean variable, `decide` or `if`, so `bool_cases` fails, and
`simp_all` closes it. -/
example (tbl : ℕ → Option (SPComp ℕ)) (dflt c : SPComp ℕ) (k : ℕ) (h : tbl k = some c) :
    lookupFresh tbl dflt k = c := by
  fail_if_success bool_cases
  simp_all [lookupFresh]

/-- The same goal, closed by `catcrypt_auto`. -/
example (tbl : ℕ → Option (SPComp ℕ)) (dflt c : SPComp ℕ) (k : ℕ) (h : tbl k = some c) :
    lookupFresh tbl dflt k = c := by
  catcrypt_auto

end CatCrypt.Tactics.AutoFixUnfoldTest
