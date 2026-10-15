/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoArms
public meta import CatCryptCore.Tactics.AutoArms
public import CatCryptCore.Crypto.SDist

/-!
# Tests for `CatCryptCore.Tactics.AutoArms`

The first part tests `hop_chain`, `sum_atoms_le` and `gcongr_unfold` on an abstract
pseudometric and abstract atoms. The second part registers `sdist`, `Advantage` and
`AdvantageA` and restates goal shapes of existing proofs as regression tests.
-/

set_option autoImplicit false

open CatCrypt.Core CatCrypt.Crypto
open scoped ENNReal

namespace CatCrypt.Tactics.AutoArmsTest

/-! ## An abstract pseudometric -/

/-- A pseudometric on `X` with values in `ℝ≥0∞`. -/
structure PM (X : Type) where
  /-- The distance. -/
  d : X → X → ℝ≥0∞
  /-- Triangle inequality. -/
  tri : ∀ x y z, d x z ≤ d x y + d y z
  /-- Symmetry. -/
  symm : ∀ x y, d x y = d y x

/-- The triangle inequality of a `PM`, stated on the distance. -/
@[hop_metric] theorem PM.d_triangle {X : Type} (M : PM X) (x y z : X) :
    M.d x z ≤ M.d x y + M.d y z := M.tri x y z

/-- The symmetry of a `PM`, stated on the distance. -/
@[hop_metric] theorem PM.d_symm {X : Type} (M : PM X) (x y : X) :
    M.d x y = M.d y x := M.symm x y

/-- A distance-valued definition, unfolded by `hop_chain`. -/
@[hop_metric] noncomputable def pmAdv {X : Type} (M : PM X) (x y : X) : ℝ≥0∞ := M.d x y

section Abstract

variable {X : Type} (M : PM X) (a b c d : X) (e₁ e₂ e₃ f g : ℝ≥0∞)

/-- Three hops, given out of order, summed left-associated. -/
example (h₂ : M.d b c ≤ e₂) (h₃ : M.d c d ≤ e₃) (h₁ : M.d a b ≤ e₁) :
    M.d a d ≤ e₁ + e₂ + e₃ := by
  hop_chain

/-- A hop used backwards through the registered symmetry lemma. -/
example (h₁ : M.d a b ≤ e₁) (h₂ : M.d c b ≤ e₂) : M.d a c ≤ e₁ + e₂ := by
  hop_chain

/-- Hops passed as arguments, a scalar bound on the right. -/
example (hab : M.d a b ≤ f) (hbc : M.d b c ≤ f) (hcd : M.d c d ≤ f) :
    M.d a d ≤ 3 * f := by
  hop_chain [hab, hbc, hcd]

/-- Residual closed by a hypothesis between atoms and a padding term. -/
example (h₁ : M.d a b ≤ e₁) (h₂ : M.d b c ≤ e₂) (hf : e₁ ≤ f) :
    M.d a c ≤ g + e₂ + f := by
  hop_chain

/-- An equality hop and a distance-valued definition in goal and hops. -/
example (h₁ : pmAdv M a b = e₁) (h₂ : pmAdv M b c ≤ e₂) : pmAdv M a c ≤ e₁ + e₂ := by
  hop_chain

/-- A quantified hypothesis is not a hop fact, and is refused as an argument. -/
example (hall : ∀ x y : X, M.d x y ≤ f) (h₁ : M.d a b ≤ e₁) : M.d a c ≤ e₁ + f := by
  fail_if_success hop_chain
  fail_if_success hop_chain [hall]
  hop_chain [hall b c]

/-- No path from `a` to `d` until the missing hop is supplied as an argument. -/
example (h₁ : M.d a b ≤ e₁) (h₂ : M.d c d ≤ e₂) : M.d a d ≤ e₁ + M.d b c + e₂ := by
  fail_if_success hop_chain
  hop_chain [le_refl (M.d b c)]

/-- A residual that needs two hypothesis steps for one atom is outside the procedure. -/
example (h₁ : M.d a b ≤ e₁) (h₂ : M.d b c ≤ e₂) (hg : e₂ ≤ g) (hgf : g ≤ f) :
    M.d a c ≤ e₁ + f := by
  fail_if_success hop_chain
  exact (M.tri a b c).trans (add_le_add h₁ (h₂.trans (hg.trans hgf)))

end Abstract

/-! ## Sums of atoms -/

section Atoms

variable (x y z w : ℝ≥0∞)

example : x + 2 * y ≤ y + z + x + y := by sum_atoms_le

example : 0 ≤ x + y := by sum_atoms_le

example : (2 : ℕ) • x ≤ x + y + x := by sum_atoms_le

example (hxz : x ≤ z) (hyw : y ≤ w) : x + y + x ≤ w + x + z + y := by sum_atoms_le

example (hxy : x ≤ y) : 2 * x ≤ x + y := by sum_atoms_le

example (hyw : y ≤ w) (hwz : w ≤ z) : x + y ≤ x + z := by
  fail_if_success sum_atoms_le
  gcongr
  exact hyw.trans hwz

end Atoms

/-! ## Monotonicity -/

/-- A scaled bound `c * x`. -/
noncomputable def scaled (c x : ℝ≥0∞) : ℝ≥0∞ := c * x

example (c : ℝ≥0∞) : Monotone (scaled c) := by gcongr_unfold [scaled]

example (c x y : ℝ≥0∞) (h : x ≤ y) : scaled c x + 1 ≤ scaled c y + 1 := by
  gcongr_unfold [scaled]

example (c : ℝ≥0∞) : Monotone (scaled c) := by
  fail_if_success gcongr_unfold [Nat.succ]
  gcongr_unfold [scaled]

/-! ## Regression: goal shapes of existing proofs -/

attribute [hop_metric] sdist_triangle sdist_sym advantage_triangle Advantage_sym
  advantageA_triangle AdvantageA_sym

/-- The `sdist` chain of `kemtls_advantage_bound` (KEMTLS/Reduction.lean). -/
example {α β : Type} (R H₁ H₂ I : α → SPComp β) (ε₁ ε₂ ε₃ : ℝ≥0∞)
    (h₁ : sdist R H₁ ≤ ε₁) (h₂ : sdist H₁ H₂ ≤ ε₂) (h₃ : sdist H₂ I ≤ ε₃) :
    sdist R I ≤ ε₁ + ε₂ + ε₃ := by
  hop_chain

/-- The `AdvantageA` chain of the OEKE reduction (OEKE/Reduction.lean): two hops with
zero advantage given as equalities; a hop at another adversary is not used. -/
example {α : Type} (G H₁ H₂ H₃ I : SPComp α) (A B : α → SPComp Bool) (ε₁ ε₂ : ℝ≥0∞)
    (h₁ : AdvantageA G H₁ A ≤ ε₁) (h₂ : AdvantageA H₁ H₂ A = 0)
    (h₃ : AdvantageA H₂ H₃ A = 0) (h₄ : AdvantageA H₃ I A ≤ ε₂)
    (_hB : AdvantageA G I B ≤ 0) :
    AdvantageA G I A ≤ ε₁ + ε₂ := by
  hop_chain

/-- A key-agreement advantage defined as an `Advantage` and equal to a DDH advantage
(`ka_secure_under_ddh`, Examples/DiffieHellman.lean), at one reduction. -/
noncomputable def kaAdv (Kr Ki : SPComp Bool) : ℝ≥0∞ := Advantage Kr Ki

attribute [hop_metric] kaAdv

example (Kr Ki : SPComp Bool) (ddh ε : ℝ≥0∞) (heq : kaAdv Kr Ki = ddh) (h : ddh ≤ ε) :
    kaAdv Kr Ki ≤ ε := by
  hop_chain

/-- The NRS21 bound (MuSig2/Reduction.lean). -/
noncomputable def nrs21Bound (qH qS qOrd : ℕ) (ε : ℝ≥0∞) : ℝ≥0∞ :=
  ((qH + qS + 1) ^ 2 : ℕ) / (qOrd : ℝ≥0∞) * ε

example (qH qS qOrd : ℕ) : Monotone (nrs21Bound qH qS qOrd) := by
  gcongr_unfold [nrs21Bound]

/-- The dictionary bound (OEKE/Reduction.lean). -/
noncomputable def dictBound (numSessions dictSize : ℕ) : ℝ≥0∞ :=
  (numSessions : ℕ) / (dictSize : ℕ)

example {q₁ q₂ : ℕ} (hle : q₁ ≤ q₂) (dictSize : ℕ) :
    dictBound q₁ dictSize ≤ dictBound q₂ dictSize := by
  gcongr_unfold [dictBound]

example (dictSize : ℕ) : Monotone (dictBound · dictSize) := by
  gcongr_unfold [dictBound]

end CatCrypt.Tactics.AutoArmsTest
