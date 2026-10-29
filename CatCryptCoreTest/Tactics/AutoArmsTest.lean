/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoArms
public meta import CatCryptCore.Tactics.AutoArms
public import CatCryptCore.Tactics.AutoMetrics
public import CatCryptCore.Crypto.UCAdmClass
public import CatCryptCore.Crypto.KEM.Games
public import CatCryptCore.Crypto.PKE.Games
public import CatCryptCore.Examples.DiffieHellman

/-!
# Tests for `CatCryptCore.Tactics.AutoArms`

The first part tests `hop_chain`, `sum_atoms_le` and `gcongr_unfold` on an abstract
pseudometric and abstract atoms. The second part restates goal shapes of existing
proofs over `sdist`, `Advantage` and `AdvantageA`, registered in
`CatCryptCore.Tactics.AutoMetrics`, as regression tests. The third part tests the
distances registered with `@[hop_metric]` at their definition sites: `UCMonad.ucCdist`,
`KA_Advantage` and the KEM and PKE `indcpaAdvantage`. The last part tests `hop_chain!`
on a bound defined as a sum and on endpoints that agree after unfolding, and
`bool_cases`. The final part tests `ord_residual` on ordered-semiring residuals in `ℝ≥0∞`,
`ℝ` and `ℕ`, directly and through `catcrypt_auto` (including a goal beside an equation
whose right side contains its left side, which the arm `simp_all` clears), and its two
failures: a goal outside its shape and a false bound that exhausts the depth.
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

/-- A sum over a literal range is read after `Finset.sum_range_succ` expands it. -/
example (f : ℕ → ℝ≥0∞) (h₀ : f 0 ≤ x) (h₁ : f 1 ≤ y) :
    ∑ i ∈ Finset.range 2, f i ≤ x + y := by
  sum_atoms_le

/-- A sum over `Finset.range (k + 1)` is read as the sum over `Finset.range k` and the
last summand. -/
example (k : ℕ) (f : ℕ → ℝ≥0∞) (h : ∑ i ∈ Finset.range k, f i ≤ x) :
    ∑ i ∈ Finset.range (k + 1), f i ≤ x + f k := by
  sum_atoms_le

/-- A conditional on a Boolean literal equation is reduced before the atoms are read. -/
example : x + (if false = true then 1 else 0) ≤ x := by
  sum_atoms_le

/-- A hypothesis bounding an atom by a sum, its summands in another order and grouping. -/
example (h : x ≤ y + z) : w + x ≤ z + (w + y) := by sum_atoms_le

/-- A hypothesis bounding a sum, its summands spread over the left side. -/
example (h : x + y ≤ z) : y + (w + x) ≤ w + z := by sum_atoms_le

/-- Two hypotheses between sums applied in sequence. -/
example (v : ℝ≥0∞) (h₁ : x + y ≤ z) (h₂ : z + w ≤ v) : (w + y) + x ≤ v := by sum_atoms_le

/-- A hypothesis between sums followed by a hypothesis between atoms. -/
example (h : x ≤ y + z) (hz : z ≤ w) : x ≤ w + y := by sum_atoms_le

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

/-- A three-hop `sdist` chain. -/
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
(`ka_advantage_eq_ddh`, Examples/DiffieHellman.lean), at one reduction. -/
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

/-! ## Distances registered at their definition sites -/

/-- `ucCdist` (`CatCryptCore.Crypto.UCAdmClass`): three hops, the middle one used
backwards through `ucCdist_sym`. -/
example {T : Type → Type} [UCMonad.UCMonadCompDist T] {α β : Type} (f g h k : α → T β)
    (e₁ e₂ e₃ : ℝ≥0∞) (h₁ : UCMonad.ucCdist f g ≤ e₁) (h₂ : UCMonad.ucCdist h g ≤ e₂)
    (h₃ : UCMonad.ucCdist h k ≤ e₃) :
    UCMonad.ucCdist f k ≤ e₁ + e₂ + e₃ := by
  hop_chain

/-- `KA_Advantage` (`CatCryptCore.Examples.DiffieHellman`), unfolded to the `Advantage`
between the real and the ideal experiment, through an intermediate game. -/
example (P : PairingGroup)
    (D : CatCrypt.Examples.DiffieHellman.KA_Distinguisher P.G₁) (G : SPComp Bool)
    (e₁ e₂ : ℝ≥0∞)
    (h₁ : Advantage (CatCrypt.Examples.DiffieHellman.KA_Game_Real P D) G ≤ e₁)
    (h₂ : Advantage (CatCrypt.Examples.DiffieHellman.KA_Game_Ideal P D) G ≤ e₂) :
    CatCrypt.Examples.DiffieHellman.KA_Advantage P D ≤ e₁ + e₂ := by
  hop_chain

/-- The KEM `indcpaAdvantage` (`CatCryptCore.Crypto.KEM.Games`), through an
intermediate game. -/
example {PK SK K C : Type} [Fintype K] [Nonempty K] (S : KEM.Games.Scheme PK SK K C)
    (A : PK → C → K → PMF Bool) (G : SPComp Bool) (e₁ e₂ : ℝ≥0∞)
    (h₁ : Advantage (liftPMF (KEM.Games.indcpaGame S A true)) G ≤ e₁)
    (h₂ : Advantage G (liftPMF (KEM.Games.indcpaGame S A false)) ≤ e₂) :
    KEM.Games.indcpaAdvantage S A ≤ e₁ + e₂ := by
  hop_chain

/-- The PKE `indcpaAdvantage` (`CatCryptCore.Crypto.PKE.Games`), through an
intermediate game, the second hop used backwards. -/
example {PK SK M C R : Type} [Fintype R] [Nonempty R] (P : PKE.Games.Scheme PK SK M C R)
    (A : PKE.Games.INDCPAAdversary PK M C) (G : SPComp Bool) (e₁ e₂ : ℝ≥0∞)
    (h₁ : Advantage (liftPMF (PKE.Games.indcpaGame P A true)) G ≤ e₁)
    (h₂ : Advantage (liftPMF (PKE.Games.indcpaGame P A false)) G ≤ e₂) :
    PKE.Games.indcpaAdvantage P A ≤ e₁ + e₂ := by
  hop_chain

/-! ## `hop_chain!` -/

/-- A bound defined as the sum of the hop bounds. -/
noncomputable def twoHopBound (ε : ℝ≥0∞) : ℝ≥0∞ := ε + ε

/-- The residual `ε + ε ≤ twoHopBound ε` is closed after unfolding `twoHopBound`. -/
example (G₀ G₁ G₂ : SPComp Bool) (ε : ℝ≥0∞) (h₁ : Advantage G₀ G₁ ≤ ε)
    (h₂ : Advantage G₁ G₂ ≤ ε) : Advantage G₀ G₂ ≤ twoHopBound ε := by
  fail_if_success hop_chain
  hop_chain!

/-- A game definition that is its argument. -/
def sameGame (G : SPComp Bool) : SPComp Bool := G

/-- The endpoints `sameGame G₁` and `G₁` of two hops agree after unfolding `sameGame`. -/
example (G₀ G₁ G₂ : SPComp Bool) (ε : ℝ≥0∞) (h₁ : Advantage G₀ (sameGame G₁) ≤ ε)
    (h₂ : Advantage G₁ G₂ ≤ ε) : Advantage G₀ G₂ ≤ 2 * ε := by
  fail_if_success hop_chain
  hop_chain!

/-- A residual that does not hold stays open. -/
example (G₀ G₁ G₂ : SPComp Bool) (ε : ℝ≥0∞) (h₁ : Advantage G₀ G₁ ≤ ε)
    (h₂ : Advantage G₁ G₂ ≤ ε) : True := by
  fail_if_success have _ : Advantage G₀ G₂ ≤ ε := by hop_chain!
  trivial

/-! ## `bool_cases` -/

/-- A Boolean variable of the goal. -/
example (b : Bool) (f : Bool → ℕ) (h : f true = 1) (h' : f false = 1) : f b = 1 := by
  bool_cases <;> simp_all

/-- The condition of an `if`. -/
example (x y : ℕ) : (if x = y then 1 else 1) = 1 := by
  bool_cases <;> simp_all

/-- A goal that holds by `rfl` after the split. -/
example (b : Bool) : (b && true) = b := by
  bool_cases <;> rfl

/-- Five Boolean variables: three rounds split `a`, `b` and `c`, leaving eight goals. -/
example (a b c d e : Bool) : (a && b && c && d && e) = (e && d && c && b && a) := by
  bool_cases
  all_goals (cases d <;> cases e <;> rfl)

/-- Without a Boolean variable, `decide` or `if` in the goal, `bool_cases` fails. -/
example (n : ℕ) : n + 0 = n := by
  fail_if_success bool_cases
  rfl

/-! ## `ord_residual` -/

example (x S : ℝ≥0∞) (h : x ≤ 1) : x * S ≤ S := by ord_residual
example (b S : ℝ≥0∞) (h : S ≤ 1) : b * S ≤ b := by ord_residual
example (p e : ℝ≥0∞) (t n : ℕ) (ht : 1 ≤ t) (hn : 1 ≤ n) :
    p + e ≤ t * p + n * e := by ord_residual
example (x S : ℝ) (h : x ≤ 1) (h0 : 0 ≤ S) : x * S ≤ S := by ord_residual
example (a n : ℕ) (h : 1 ≤ n) : a ≤ n * a := by ord_residual
example (R b c S : ℝ≥0∞) (h1 : R ≤ b) (h2 : c ≤ 1) : R + c * S ≤ b + S := by
  ord_residual

example (x S : ℝ≥0∞) (h : x ≤ 1) : x * S ≤ S := by catcrypt_auto
example (p e : ℝ≥0∞) (t n : ℕ) (ht : 1 ≤ t) (hn : 1 ≤ n) :
    p + e ≤ t * p + n * e := by catcrypt_auto
/-- The looping equation `_hQ` stays in the context; `catcrypt_auto` must not hand it to
`simp_all` unguarded. -/
example (S c b : ℝ≥0∞) (_hQ : S = c * S + b * S) (_h : c ≤ 1) (hS : S ≤ 1) :
    b * S ≤ b := by catcrypt_auto

/-- error: ord_residual: the goal is not `_ ≤ _` over an ordered semiring -/
#guard_msgs in
example (a b : ℕ) : a = b := by ord_residual

/--
error: ord_residual: no step closes
  x * S ≤ S
-/
#guard_msgs in
example (x S : ℝ≥0∞) : x * S ≤ S := by ord_residual

end CatCrypt.Tactics.AutoArmsTest
