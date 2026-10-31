/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCLoopbackObservation
public import CatCryptCore.Quantum.QSysCatOpenTheory

/-!
# Quantitative emulation over a PolyFun open theory

Quantitative emulation compares two open systems of a PolyFun `OpenTheory` `T` through an
observation boundary `Ω`. A test of an open system on `Δ` is an open system `K` on
`Δ.swap ⊗ Ω`; the run of `W` against `K` is the sequential composite `seq W K`, the system `W`
seen on `empty ⊗ Δ` and wired with `K` along `Δ`. An observation map `obs : T.Obj Ω → X`
reads off what a run shows, and an extended pseudometric `D` on `X` measures how far two
observations are apart. `real` emulates `ideal` up to `ε` (`EmulatesObs D obs ε real ideal`)
when for every test the observations of the two runs are at distance at most `ε`. At `ε = 0`
with the discrete distance this is observational equivalence (testing equivalence).

Emulation up to `ε` is reflexive at `0`, symmetric, and satisfies the triangle inequality with
the bounds added. It is closed under sequential composition for every traced open theory
(`seq_seq`, from wire associativity). Closure under `map`, parallel composition and wiring uses
`TestFactorization T Ω`: a test of a composite is a test of the component, uniformly in the
component. The right-hand forms follow from the commutativity laws of `par` and `wire`.

The classical open theory `loopOpenTheory` and the quantum open theory `qOpenTheory R` on the
Int construction both satisfy `TestFactorization` over the bit boundary, and their testing
equivalences `EmulatesΩ` (classical and quantum UC emulation) are `EmulatesObs` at `0` for the
discrete distance on the bit observation `obsBit`.

## Main definitions

* `ObsDist X`: an extended pseudometric on `X`; `ObsDist.ofEMetric`, `ObsDist.discrete`.
* `OpenTheoryObs.seq`: sequential composition of an open system with a context.
* `OpenTheoryObs.TestFactorization T Ω`: tests of `map`, `par` and `wire` composites factor
  through tests of the component.
* `OpenTheoryObs.EmulatesObs D obs ε real ideal`: quantitative emulation.

## Main results

* `seq_seq`: sequential composition is associative in a traced open theory.
* `EmulatesObs.refl`, `EmulatesObs.symm`, `EmulatesObs.trans`, `EmulatesObs.mono`.
* `EmulatesObs.seq_left`, `EmulatesObs.seq_right`, `EmulatesObs.map`,
  `EmulatesObs.par_left`, `EmulatesObs.par_right`, `EmulatesObs.wire_left`,
  `EmulatesObs.wire_right`: closure with the same `ε`.
* `EmulatesObs.par_compose`, `EmulatesObs.wire_compose`, `EmulatesObs.seq_compose`: the
  composition theorems, with the bounds added.
* `loop_testFactorization`, `emulatesΩ_iff_emulatesObs`: the classical instance.
* `q_testFactorization`, `qEmulatesΩ_iff_emulatesObs`: the quantum UC instance.
-/

set_option autoImplicit false

@[expose] public section

open scoped ENNReal

namespace CatCrypt.Crypto

/-- An extended pseudometric on `X`, given as data: a distance that vanishes on the diagonal,
is symmetric, and satisfies the triangle inequality. -/
structure ObsDist (X : Type*) where
  /-- The distance of two observations. -/
  dist : X → X → ℝ≥0∞
  /-- The distance of an observation to itself is `0`. -/
  dist_self : ∀ x, dist x x = 0
  /-- The distance is symmetric. -/
  dist_comm : ∀ x y, dist x y = dist y x
  /-- The triangle inequality. -/
  dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z

namespace ObsDist

/-- The extended distance of a pseudo extended metric space. -/
def ofEMetric (X : Type*) [PseudoEMetricSpace X] : ObsDist X where
  dist := edist
  dist_self := edist_self
  dist_comm := edist_comm
  dist_triangle := edist_triangle

open Classical in
/-- The discrete distance: `0` on equal observations, `⊤` otherwise. -/
noncomputable def discrete (X : Type*) : ObsDist X where
  dist x y := if x = y then 0 else ⊤
  dist_self x := by simp
  dist_comm x y := by
    by_cases h : x = y
    · simp [h]
    · simp [h, Ne.symm h]
  dist_triangle x y z := by
    by_cases hxy : x = y
    · subst hxy; simp
    · simp [hxy]

/-- Two observations are at discrete distance at most `0` exactly when they are equal. -/
theorem discrete_le_zero {X : Type*} {x y : X} : (discrete X).dist x y ≤ 0 ↔ x = y := by
  classical
  by_cases h : x = y
  · simp [discrete, h]
  · simp [discrete, h]

end ObsDist

namespace OpenTheoryObs

open Interaction Interaction.Open

universe u

section Generic

variable {T : OpenTheory.{u}}

/-- Sequential composition: the open system `W` on `Δ`, seen on `empty ⊗ Δ`, wired with the
context `C` along `Δ`, on the boundary `Δ'`. The run of `W` against a test on `Δ.swap ⊗ Ω` is
`seq T W K`. -/
def seq (T : OpenTheory.{u}) [OpenTheory.HasUnit T] {Δ Δ' : PortBoundary} (W : T.Obj Δ)
    (C : T.Obj (Δ.swap.tensor Δ')) : T.Obj Δ' :=
  T.map (PortBoundary.Equiv.tensorEmptyLeft Δ').toHom
    (T.wire (T.par (OpenTheory.HasUnit.unit (T := T)) W) C)

/-- Putting the unit beside an object of `empty ⊗ Δ` read on `Δ` gives the object back. -/
theorem par_unit_map [OpenTheory.IsMonoidal T] {Δ : PortBoundary}
    (Y : T.Obj (PortBoundary.empty.tensor Δ)) :
    T.par (OpenTheory.HasUnit.unit (T := T))
      (T.map (PortBoundary.Equiv.tensorEmptyLeft Δ).toHom Y) = Y := by
  have h := OpenTheory.par_leftUnit (T := T)
    (T.map (PortBoundary.Equiv.tensorEmptyLeft Δ).toHom Y)
  calc _ = T.mapEquiv (PortBoundary.Equiv.tensorEmptyLeft Δ).symm
        (T.mapEquiv (PortBoundary.Equiv.tensorEmptyLeft Δ)
          (T.par (OpenTheory.HasUnit.unit (T := T))
            (T.map (PortBoundary.Equiv.tensorEmptyLeft Δ).toHom Y))) :=
        (OpenTheory.mapEquiv_symm_cancel _ _).symm
    _ = Y := by rw [h]; exact OpenTheory.mapEquiv_symm_cancel _ _

/-- Sequential composition is associative: running `seq T W C` against `K` is running `W`
against the wiring of `C` with `K`. -/
theorem seq_seq [OpenTheory.IsTraced T] {Δ Δ' Δ'' : PortBoundary} (W : T.Obj Δ)
    (C : T.Obj (Δ.swap.tensor Δ')) (K : T.Obj (Δ'.swap.tensor Δ'')) :
    seq T (seq T W C) K = seq T W (T.wire C K) := by
  simp only [seq]
  rw [par_unit_map, OpenTheory.wire_assoc]

/-- Tests of a `map`, `par` or `wire` composite factor through tests of the component: for a
fixed context and test there is a test of the component with the same run, whatever the
component. -/
class TestFactorization (T : OpenTheory.{u}) [OpenTheory.HasUnit T] (Ω : PortBoundary) :
    Prop where
  /-- Tests of `map f W` factor through tests of `W`. -/
  map : ∀ {Δ Δ' : PortBoundary} (f : PortBoundary.Hom Δ Δ')
    (K : T.Obj (Δ'.swap.tensor Ω)), ∃ K' : T.Obj (Δ.swap.tensor Ω),
      ∀ W : T.Obj Δ, seq T (T.map f W) K = seq T W K'
  /-- Tests of `par W C` factor through tests of `W`. -/
  par_left : ∀ {Δ₁ Δ₂ : PortBoundary} (C : T.Obj Δ₂)
    (K : T.Obj ((Δ₁.tensor Δ₂).swap.tensor Ω)), ∃ K' : T.Obj (Δ₁.swap.tensor Ω),
      ∀ W : T.Obj Δ₁, seq T (T.par W C) K = seq T W K'
  /-- Tests of `wire W C` factor through tests of `W`. -/
  wire_left : ∀ {Δ₁ Γ Δ₂ : PortBoundary} (C : T.Obj (Γ.swap.tensor Δ₂))
    (K : T.Obj ((Δ₁.tensor Δ₂).swap.tensor Ω)),
      ∃ K' : T.Obj ((Δ₁.tensor Γ).swap.tensor Ω),
      ∀ W : T.Obj (Δ₁.tensor Γ), seq T (T.wire W C) K = seq T W K'

/-- Quantitative emulation: `real` emulates `ideal` up to `ε` when, for every test `K`, the
observations of the runs of `real` and `ideal` against `K` are at distance at most `ε`. -/
def EmulatesObs [OpenTheory.HasUnit T] {Ω : PortBoundary} {X : Type*} (D : ObsDist X)
    (obs : T.Obj Ω → X) (ε : ℝ≥0∞) {Δ : PortBoundary} (real ideal : T.Obj Δ) : Prop :=
  ∀ K : T.Obj (Δ.swap.tensor Ω), D.dist (obs (seq T real K)) (obs (seq T ideal K)) ≤ ε

namespace EmulatesObs

variable {Ω : PortBoundary} {X : Type*} {D : ObsDist X} {Δ : PortBoundary}

section Unit

variable [OpenTheory.HasUnit T] {obs : T.Obj Ω → X}

/-- Every open system emulates itself up to `0`. -/
theorem refl (W : T.Obj Δ) : EmulatesObs D obs 0 W W := fun K => by
  rw [D.dist_self]

/-- Emulation up to `ε` is symmetric. -/
theorem symm {ε : ℝ≥0∞} {W₁ W₂ : T.Obj Δ} (h : EmulatesObs D obs ε W₁ W₂) :
    EmulatesObs D obs ε W₂ W₁ := fun K => by
  rw [D.dist_comm]
  exact h K

/-- Emulation up to `ε` is monotone in `ε`. -/
theorem mono {ε ε' : ℝ≥0∞} {W₁ W₂ : T.Obj Δ} (h : EmulatesObs D obs ε W₁ W₂) (hε : ε ≤ ε') :
    EmulatesObs D obs ε' W₁ W₂ := fun K => (h K).trans hε

/-- **Triangle inequality.** -/
theorem trans {ε₁ ε₂ : ℝ≥0∞} {W₁ W₂ W₃ : T.Obj Δ} (h₁₂ : EmulatesObs D obs ε₁ W₁ W₂)
    (h₂₃ : EmulatesObs D obs ε₂ W₂ W₃) : EmulatesObs D obs (ε₁ + ε₂) W₁ W₃ := fun K =>
  (D.dist_triangle _ _ _).trans (add_le_add (h₁₂ K) (h₂₃ K))

variable [TestFactorization T Ω]

/-- Emulation up to `ε` is invariant under `map`. -/
theorem map {Δ' : PortBoundary} {ε : ℝ≥0∞} (f : PortBoundary.Hom Δ Δ')
    {real ideal : T.Obj Δ} (h : EmulatesObs D obs ε real ideal) :
    EmulatesObs D obs ε (T.map f real) (T.map f ideal) := fun K => by
  obtain ⟨K', hK'⟩ := TestFactorization.map f K
  rw [hK', hK']
  exact h K'

/-- Putting a context `C` in parallel on the right preserves emulation up to `ε`. -/
theorem par_left {Δ₂ : PortBoundary} {ε : ℝ≥0∞} {real ideal : T.Obj Δ}
    (h : EmulatesObs D obs ε real ideal) (C : T.Obj Δ₂) :
    EmulatesObs D obs ε (T.par real C) (T.par ideal C) := fun K => by
  obtain ⟨K', hK'⟩ := TestFactorization.par_left C K
  rw [hK', hK']
  exact h K'

/-- Wiring a context `C` on the right preserves emulation up to `ε`. -/
theorem wire_left {Δ₁ Γ Δ₂ : PortBoundary} {ε : ℝ≥0∞} {real ideal : T.Obj (Δ₁.tensor Γ)}
    (h : EmulatesObs D obs ε real ideal) (C : T.Obj (Γ.swap.tensor Δ₂)) :
    EmulatesObs D obs ε (T.wire real C) (T.wire ideal C) := fun K => by
  obtain ⟨K', hK'⟩ := TestFactorization.wire_left C K
  rw [hK', hK']
  exact h K'

end Unit

section Monoidal

variable [OpenTheory.IsMonoidal T] {obs : T.Obj Ω → X} [TestFactorization T Ω]

/-- Putting a context `C` in parallel on the left preserves emulation up to `ε`. -/
theorem par_right {Δ₁ : PortBoundary} {ε : ℝ≥0∞} (C : T.Obj Δ₁)
    {real ideal : T.Obj Δ} (h : EmulatesObs D obs ε real ideal) :
    EmulatesObs D obs ε (T.par C real) (T.par C ideal) := by
  rw [← OpenTheory.par_comm real C, ← OpenTheory.par_comm ideal C]
  exact (h.par_left C).map _

/-- **Composition theorem for `par`.** -/
theorem par_compose {Δ₂ : PortBoundary} {ε₁ ε₂ : ℝ≥0∞}
    {real₁ ideal₁ : T.Obj Δ} {real₂ ideal₂ : T.Obj Δ₂} (h₁ : EmulatesObs D obs ε₁ real₁ ideal₁)
    (h₂ : EmulatesObs D obs ε₂ real₂ ideal₂) :
    EmulatesObs D obs (ε₁ + ε₂) (T.par real₁ real₂) (T.par ideal₁ ideal₂) :=
  (h₁.par_left real₂).trans (par_right ideal₁ h₂)

end Monoidal

section Traced

variable [OpenTheory.IsTraced T] {obs : T.Obj Ω → X}

/-- Sequential composition with a context on the right preserves emulation up to `ε`. -/
theorem seq_left {Δ' : PortBoundary} {ε : ℝ≥0∞}
    {real ideal : T.Obj Δ} (h : EmulatesObs D obs ε real ideal)
    (C : T.Obj (Δ.swap.tensor Δ')) : EmulatesObs D obs ε (seq T real C) (seq T ideal C) :=
  fun K => by
    rw [seq_seq, seq_seq]
    exact h _

variable [TestFactorization T Ω]

/-- Wiring a context `C` on the left preserves emulation up to `ε`. -/
theorem wire_right {Δ₁ Γ Δ₂ : PortBoundary} {ε : ℝ≥0∞}
    (C : T.Obj (Δ₁.tensor Γ)) {real ideal : T.Obj (Γ.swap.tensor Δ₂)}
    (h : EmulatesObs D obs ε real ideal) :
    EmulatesObs D obs ε (T.wire C real) (T.wire C ideal) := by
  rw [OpenTheory.wire_comm C real, OpenTheory.wire_comm C ideal]
  exact ((h.map _).wire_left _).map _

/-- Sequential composition with a context on the left preserves emulation up to `ε`. -/
theorem seq_right {Δ₀ : PortBoundary} {ε : ℝ≥0∞} (W : T.Obj Δ₀)
    {real ideal : T.Obj (Δ₀.swap.tensor Δ)} (h : EmulatesObs D obs ε real ideal) :
    EmulatesObs D obs ε (seq T W real) (seq T W ideal) :=
  (h.wire_right _).map _

/-- **Composition theorem for `wire`.** -/
theorem wire_compose {Δ₁ Γ Δ₂ : PortBoundary} {ε₁ ε₂ : ℝ≥0∞}
    {real₁ ideal₁ : T.Obj (Δ₁.tensor Γ)} {real₂ ideal₂ : T.Obj (Γ.swap.tensor Δ₂)}
    (h₁ : EmulatesObs D obs ε₁ real₁ ideal₁) (h₂ : EmulatesObs D obs ε₂ real₂ ideal₂) :
    EmulatesObs D obs (ε₁ + ε₂) (T.wire real₁ real₂) (T.wire ideal₁ ideal₂) :=
  (h₁.wire_left real₂).trans (wire_right ideal₁ h₂)

/-- **Composition theorem for sequential composition.** -/
theorem seq_compose {Δ' : PortBoundary} {ε₁ ε₂ : ℝ≥0∞}
    {real₁ ideal₁ : T.Obj Δ} {real₂ ideal₂ : T.Obj (Δ.swap.tensor Δ')}
    (h₁ : EmulatesObs D obs ε₁ real₁ ideal₁) (h₂ : EmulatesObs D obs ε₂ real₂ ideal₂) :
    EmulatesObs D obs (ε₁ + ε₂) (seq T real₁ real₂) (seq T ideal₁ ideal₂) :=
  (h₁.seq_left real₂).trans (seq_right ideal₁ h₂)

end Traced

end EmulatesObs

end Generic

/-! ## The classical instance -/

section Loop

open CatCrypt.Core CategoryTheory MonoidalCategory
open CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.SysCat
open CatCrypt.Crypto.UCTransparent.IntSys CatCrypt.Crypto.UCLoopbackOpenTheory
open CatCrypt.Crypto.UCLoopbackObservation

/-- The test named by a morphism into the bit boundary names that morphism. -/
theorem loop_testHom_name {Δ : PortBoundary} (h : bObj Δ ⟶ bObj bitBoundary) :
    testHom (nameEquiv (bObj Δ) (bObj bitBoundary) h ≫ (bMu Δ.swap bitBoundary).hom) = h := by
  simp [testHom]

/-- Tests of `W ≫ g` factor through tests of `W`. -/
theorem loop_seq_comp {Δ Δ' : PortBoundary} (g : bObj Δ ⟶ bObj Δ')
    (K : loopOpenTheory.Obj (Δ'.swap.tensor bitBoundary)) :
    ∃ K' : loopOpenTheory.Obj (Δ.swap.tensor bitBoundary), ∀ W : loopOpenTheory.Obj Δ,
      seq loopOpenTheory (Δ := Δ') (W ≫ g) K = seq loopOpenTheory W K' :=
  ⟨nameEquiv _ _ (g ≫ testHom K) ≫ (bMu Δ.swap bitBoundary).hom, fun W => by
    change runTest _ _ = runTest _ _
    rw [runTest_eq, runTest_eq, loop_testHom_name, Category.assoc]⟩

/-- Tests of composites in `loopOpenTheory` factor through tests of the component. -/
instance loop_testFactorization : TestFactorization loopOpenTheory bitBoundary where
  map f K := loop_seq_comp (bMap f) K
  par_left {Δ₁ Δ₂} C K := by
    obtain ⟨K', hK'⟩ := loop_seq_comp ((ρ_ (bObj Δ₁)).inv ≫ bObj Δ₁ ◁ C ≫ (bMu Δ₁ Δ₂).hom) K
    refine ⟨K', fun W => ?_⟩
    have hp : loopOpenTheory.par W C =
        W ≫ ((ρ_ (bObj Δ₁)).inv ≫ bObj Δ₁ ◁ C ≫ (bMu Δ₁ Δ₂).hom) := by
      change (λ_ _).inv ≫ (W ⊗ₘ C) ≫ (bMu Δ₁ Δ₂).hom = _
      rw [MonoidalCategory.tensorHom_def, unitors_inv_equal, Category.assoc,
        ← rightUnitor_inv_naturality_assoc]
    rw [hp]
    exact hK' W
  wire_left {Δ₁ Γ Δ₂} C K := by
    obtain ⟨K', hK'⟩ := loop_seq_comp ((bMu Δ₁ Γ).inv ≫ bObj Δ₁ ◁
      (nameEquiv (bObj Γ) (bObj Δ₂)).symm (C ≫ (bMu Γ.swap Δ₂).inv) ≫ (bMu Δ₁ Δ₂).hom) K
    refine ⟨K', fun W => ?_⟩
    have hw : loopOpenTheory.wire W C =
        W ≫ ((bMu Δ₁ Γ).inv ≫ bObj Δ₁ ◁ (nameEquiv (bObj Γ) (bObj Δ₂)).symm
          (C ≫ (bMu Γ.swap Δ₂).inv) ≫ (bMu Δ₁ Δ₂).hom) := by
      simp only [wireHom, Category.assoc]
    rw [hw]
    exact hK' W

/-- Classical testing equivalence `EmulatesΩ` is quantitative emulation at `0` for the discrete
distance on the bit observation. -/
theorem emulatesΩ_iff_emulatesObs {Δ : PortBoundary} {real ideal : loopOpenTheory.Obj Δ} :
    EmulatesΩ real ideal ↔ EmulatesObs (ObsDist.discrete _) obsBit 0 real ideal := by
  simp only [EmulatesΩ, EmulatesObs, ObsDist.discrete_le_zero]
  rfl

end Loop

/-! ## The quantum instance -/

section Quantum

open CategoryTheory MonoidalCategory
open CatCrypt.Quantum.ReactiveUC CatCrypt.Quantum.ReactiveUC.QSysCat
open CatCrypt.Quantum.ReactiveUC.IntQSys CatCrypt.Quantum.ReactiveUC.QOpenTheory
open CatCrypt.Crypto.UCOpenTheory CatCrypt.Crypto.UCLoopbackOpenTheory
open CatCrypt.Crypto.UCLoopbackObservation (bitBoundary)

variable {R : Type} [Fintype R]

/-- The quantum test named by a morphism into the bit boundary names that morphism. -/
theorem q_testHom_name {Δ : PortBoundary} (h : bObj R Δ ⟶ bObj R bitBoundary) :
    QOpenTheory.testHom
      (nameEquiv (bObj R Δ) (bObj R bitBoundary) h ≫ (bMu R Δ.swap bitBoundary).hom) = h := by
  simp [QOpenTheory.testHom]

/-- Tests of `W ≫ g` factor through tests of `W`, in `qOpenTheory R`. -/
theorem q_seq_comp {Δ Δ' : PortBoundary} (g : bObj R Δ ⟶ bObj R Δ')
    (K : (qOpenTheory R).Obj (Δ'.swap.tensor bitBoundary)) :
    ∃ K' : (qOpenTheory R).Obj (Δ.swap.tensor bitBoundary), ∀ W : (qOpenTheory R).Obj Δ,
      seq (qOpenTheory R) (Δ := Δ') (W ≫ g) K = seq (qOpenTheory R) W K' :=
  ⟨nameEquiv _ _ (g ≫ QOpenTheory.testHom K) ≫ (bMu R Δ.swap bitBoundary).hom, fun W => by
    change QOpenTheory.runTest _ _ = QOpenTheory.runTest _ _
    rw [QOpenTheory.runTest_eq, QOpenTheory.runTest_eq, q_testHom_name, Category.assoc]⟩

/-- Tests of composites in `qOpenTheory R` factor through tests of the component. -/
instance q_testFactorization : TestFactorization (qOpenTheory R) bitBoundary where
  map f K := q_seq_comp (QOpenTheory.bMap (R := R) f) K
  par_left {Δ₁ Δ₂} C K := by
    obtain ⟨K', hK'⟩ :=
      q_seq_comp ((ρ_ (bObj R Δ₁)).inv ≫ bObj R Δ₁ ◁ C ≫ (bMu R Δ₁ Δ₂).hom) K
    refine ⟨K', fun W => ?_⟩
    have hp : (qOpenTheory R).par W C =
        W ≫ ((ρ_ (bObj R Δ₁)).inv ≫ bObj R Δ₁ ◁ C ≫ (bMu R Δ₁ Δ₂).hom) := by
      change (λ_ _).inv ≫ (W ⊗ₘ C) ≫ (bMu R Δ₁ Δ₂).hom = _
      rw [MonoidalCategory.tensorHom_def, unitors_inv_equal, Category.assoc,
        ← rightUnitor_inv_naturality_assoc]
    rw [hp]
    exact hK' W
  wire_left {Δ₁ Γ Δ₂} C K := by
    obtain ⟨K', hK'⟩ := q_seq_comp ((bMu R Δ₁ Γ).inv ≫ bObj R Δ₁ ◁
      (nameEquiv (bObj R Γ) (bObj R Δ₂)).symm (C ≫ (bMu R Γ.swap Δ₂).inv) ≫
        (bMu R Δ₁ Δ₂).hom) K
    refine ⟨K', fun W => ?_⟩
    have hw : (qOpenTheory R).wire W C =
        W ≫ ((bMu R Δ₁ Γ).inv ≫ bObj R Δ₁ ◁ (nameEquiv (bObj R Γ) (bObj R Δ₂)).symm
          (C ≫ (bMu R Γ.swap Δ₂).inv) ≫ (bMu R Δ₁ Δ₂).hom) := by
      simp only [QOpenTheory.wireHom, Category.assoc]
    rw [hw]
    exact hK' W

/-- Quantum UC emulation `EmulatesΩ` is quantitative emulation at `0` for the discrete distance
on the quantum bit observation. -/
theorem qEmulatesΩ_iff_emulatesObs {Δ : PortBoundary} {real ideal : (qOpenTheory R).Obj Δ} :
    QOpenTheory.EmulatesΩ real ideal ↔
      EmulatesObs (ObsDist.discrete _) QOpenTheory.obsBit 0 real ideal := by
  simp only [QOpenTheory.EmulatesΩ, EmulatesObs, ObsDist.discrete_le_zero]
  rfl

end Quantum

end OpenTheoryObs

end CatCrypt.Crypto
