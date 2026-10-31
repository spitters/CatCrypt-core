/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCLoopbackOpenTheory
public import CatCryptCore.Crypto.UCLoopbackOmega

/-!
# Testing equivalence of open systems through a bitBoundary boundary

The closed systems of `loopOpenTheory` have no events, so any two of them are equal
(`UCLoopbackOpenTheory.closed_eq`). Open systems are compared here through the bitBoundary
boundary `bitBoundary`, whose input is one start packet and whose output is one bit. A test of an
open system on `Δ` is an open system `K` on `Δ.swap ⊗ bitBoundary`; the system and the test are
wired along `Δ`, which in `IntConstruction SysCat` runs the feedback of the wire through the
unbounded loopback `Sys.loopbackω` (the trace of `SysCat`). The observation `obsBit` of the
result is the bit returned by its first activation on the start packet, a computation of
`SPComp Bool` whose missing mass is divergence or failure.

* `obsBit`: the observation of an open system on `bitBoundary`, well defined on step-equivalence
  classes (`obsBit_stepEq`).
* `EmulatesΩ real ideal`: every test observes the same bit distribution.
* `EmulatesΩ.refl`, `EmulatesΩ.symm`, `EmulatesΩ.trans`, `EmulatesΩ.map`.
* `EmulatesΩ.comp`: emulation is preserved by composition with any morphism of the Int
  construction; the composition theorems `EmulatesΩ.wire_compose` and
  `EmulatesΩ.par_compose` follow by moving the context into the test.
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.UCLoopbackObservation

open CatCrypt.Core CategoryTheory MonoidalCategory
open CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.SysCat
open CatCrypt.Crypto.UCTransparent.IntSys CatCrypt.Crypto.UCLoopbackOpenTheory
open Interaction Interaction.Open

/-! ## The first activation of a bundled system -/

/-- The output of the first activation of the bundled system `A` on the event `e`. -/
noncomputable def firstOut {E O : Type} (A : SysObj E O) (e : E) : SPComp O :=
  SPComp.map Prod.snd (A.sys.step A.sys.init e)

/-- Step-equivalent systems have the same first activation. -/
theorem firstOut_stepEq {E O : Type} {A B : SysObj E O} (h : Sys.StepEq A B) (e : E) :
    firstOut A e = firstOut B e := by
  induction h with
  | rel A B h =>
    obtain ⟨Inv, f, h⟩ := h
    simp only [firstOut]
    rw [← h.init_map, ← h.step _ e h.init_inv, SPComp.map_comp]
    rfl
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ## The bitBoundary boundary and the observation -/

/-- The bitBoundary boundary: one input port carrying the start packet and one output port carrying
a bit. -/
def bitBoundary : PortBoundary :=
  ⟨⟨Unit, fun _ => Unit⟩, ⟨Unit, fun _ => Bool⟩⟩

/-- The start packet of the bitBoundary boundary. -/
def startPkt : Interface.Packet bitBoundary.In :=
  ⟨(), ()⟩

/-- The bit of an output of a system on the bitBoundary boundary. -/
def bitOf : ((bObj bitBoundary).pos ⊗ (𝟙_ (IntConstruction SysCat)).neg).P → Bool :=
  Sum.elim (fun p => p.2) (fun e => Empty.elim e)

/-- The observation of an open system on the bitBoundary boundary: the bit returned by the first
activation of a representative on the start packet. -/
noncomputable def obsBit (W : loopOpenTheory.Obj bitBoundary) : SPComp Bool :=
  Quotient.lift (fun A => SPComp.map bitOf (firstOut A (Sum.inr startPkt)))
    (fun _ _ h => congrArg (SPComp.map bitOf) (firstOut_stepEq h _)) W.hom

/-- `obsBit` respects step equivalence of representatives. -/
theorem obsBit_stepEq
    {A B : SysObj ((𝟙_ (IntConstruction SysCat)).pos ⊗ (bObj bitBoundary).neg).P
      ((bObj bitBoundary).pos ⊗ (𝟙_ (IntConstruction SysCat)).neg).P}
    (h : Sys.StepEq A B) :
    obsBit ⟨⟦A⟧⟩ = obsBit ⟨⟦B⟧⟩ := by
  rw [Quotient.sound h]

/-! ## Tests -/

/-- The morphism `bObj Δ ⟶ bObj bitBoundary` named by the test `K`. -/
noncomputable def testHom {Δ : PortBoundary}
    (K : loopOpenTheory.Obj (Δ.swap.tensor bitBoundary)) :
    bObj Δ ⟶ bObj bitBoundary :=
  (nameEquiv (bObj Δ) (bObj bitBoundary)).symm (K ≫ (bMu Δ.swap bitBoundary).inv)

/-- The run of the open system `W` against the test `K`: `W`, seen on `empty ⊗ Δ`, wired with
`K` along `Δ`, on the boundary `bitBoundary`. -/
noncomputable def runTest {Δ : PortBoundary} (W : loopOpenTheory.Obj Δ)
    (K : loopOpenTheory.Obj (Δ.swap.tensor bitBoundary)) : loopOpenTheory.Obj bitBoundary :=
  loopOpenTheory.map (PortBoundary.Equiv.tensorEmptyLeft bitBoundary).toHom
    (loopOpenTheory.wire (loopOpenTheory.par (OpenTheory.HasUnit.unit (T := loopOpenTheory)) W)
      K)

/-- The run against a test is composition with the morphism the test names. -/
theorem runTest_eq {Δ : PortBoundary} (W : loopOpenTheory.Obj Δ)
    (K : loopOpenTheory.Obj (Δ.swap.tensor bitBoundary)) :
    runTest W K = W ≫ testHom K := by
  change (wireHom (((λ_ _).inv ≫ (bUnit.hom ⊗ₘ W) ≫ (bMu _ _).hom) ≫ (bMu _ _).inv)
    (K ≫ (bMu _ _).inv) ≫ (bMu _ _).hom) ≫ bMap _ = _
  simp only [wireHom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [MonoidalCategory.tensorHom_def', Category.assoc, ← whisker_exchange_assoc,
    bMu_leftUnit, ← MonoidalCategory.whiskerLeft_comp_assoc, leftUnitor_naturality,
    Iso.inv_hom_id_assoc]
  rfl

/-! ## Emulation against every test -/

/-- `real` emulates `ideal` when every test observes the same bit distribution. -/
def EmulatesΩ {Δ : PortBoundary} (real ideal : loopOpenTheory.Obj Δ) : Prop :=
  ∀ K : loopOpenTheory.Obj (Δ.swap.tensor bitBoundary),
    obsBit (runTest real K) = obsBit (runTest ideal K)

/-- Emulation is equality of the observations after every morphism into `bObj bitBoundary`. -/
theorem emulatesΩ_iff {Δ : PortBoundary} {real ideal : loopOpenTheory.Obj Δ} :
    EmulatesΩ real ideal ↔
      ∀ h : bObj Δ ⟶ bObj bitBoundary, obsBit (real ≫ h) = obsBit (ideal ≫ h) := by
  constructor
  · intro H h
    have hK : testHom (nameEquiv (bObj Δ) (bObj bitBoundary) h ≫
        (bMu Δ.swap bitBoundary).hom) = h := by
      simp [testHom]
    have := H (nameEquiv (bObj Δ) (bObj bitBoundary) h ≫ (bMu Δ.swap bitBoundary).hom)
    rwa [runTest_eq, runTest_eq, hK] at this
  · intro H K
    rw [runTest_eq, runTest_eq]
    exact H _

namespace EmulatesΩ

variable {Δ : PortBoundary}

/-- Every open system emulates itself. -/
theorem refl (W : loopOpenTheory.Obj Δ) : EmulatesΩ W W :=
  fun _ => rfl

/-- Emulation is symmetric. -/
theorem symm {W₁ W₂ : loopOpenTheory.Obj Δ} (h : EmulatesΩ W₁ W₂) : EmulatesΩ W₂ W₁ :=
  fun K => (h K).symm

/-- Emulation is transitive. -/
theorem trans {W₁ W₂ W₃ : loopOpenTheory.Obj Δ} (h₁₂ : EmulatesΩ W₁ W₂)
    (h₂₃ : EmulatesΩ W₂ W₃) : EmulatesΩ W₁ W₃ :=
  fun K => (h₁₂ K).trans (h₂₃ K)

/-- Emulation is preserved by composition with a morphism of the Int construction. -/
theorem comp {Δ' : PortBoundary} {real ideal : loopOpenTheory.Obj Δ} (h : EmulatesΩ real ideal)
    (g : bObj Δ ⟶ bObj Δ') : EmulatesΩ (real ≫ g) (ideal ≫ g) := by
  rw [emulatesΩ_iff] at h ⊢
  intro k
  simpa only [Category.assoc] using h (g ≫ k)

/-- Emulation is invariant under `map`. -/
theorem map {Δ' : PortBoundary} (f : PortBoundary.Hom Δ Δ') {real ideal : loopOpenTheory.Obj Δ}
    (h : EmulatesΩ real ideal) :
    EmulatesΩ (loopOpenTheory.map f real) (loopOpenTheory.map f ideal) :=
  h.comp (bMap f)

/-- Wiring a context `C` on the right preserves emulation. -/
theorem wire_left {Δ₁ Γ Δ₂ : PortBoundary} {real ideal : loopOpenTheory.Obj (Δ₁.tensor Γ)}
    (h : EmulatesΩ real ideal) (C : loopOpenTheory.Obj (Γ.swap.tensor Δ₂)) :
    EmulatesΩ (loopOpenTheory.wire real C) (loopOpenTheory.wire ideal C) := by
  have hw : ∀ W : loopOpenTheory.Obj (Δ₁.tensor Γ), loopOpenTheory.wire W C =
      W ≫ ((bMu Δ₁ Γ).inv ≫ bObj Δ₁ ◁ (nameEquiv (bObj Γ) (bObj Δ₂)).symm
        (C ≫ (bMu Γ.swap Δ₂).inv) ≫ (bMu Δ₁ Δ₂).hom) := fun W => by
    simp only [wireHom, Category.assoc]
  rw [hw, hw]
  exact h.comp _

/-- Wiring a context `C` on the left preserves emulation. -/
theorem wire_right {Δ₁ Γ Δ₂ : PortBoundary} (C : loopOpenTheory.Obj (Δ₁.tensor Γ))
    {real ideal : loopOpenTheory.Obj (Γ.swap.tensor Δ₂)} (h : EmulatesΩ real ideal) :
    EmulatesΩ (loopOpenTheory.wire C real) (loopOpenTheory.wire C ideal) := by
  rw [wire_comm' C real, wire_comm' C ideal]
  exact ((h.map _).wire_left _).map _

/-- Putting a context `C` in parallel on the right preserves emulation. -/
theorem par_left {Δ₁ Δ₂ : PortBoundary} {real ideal : loopOpenTheory.Obj Δ₁}
    (h : EmulatesΩ real ideal) (C : loopOpenTheory.Obj Δ₂) :
    EmulatesΩ (loopOpenTheory.par real C) (loopOpenTheory.par ideal C) := by
  have hp : ∀ W : loopOpenTheory.Obj Δ₁, loopOpenTheory.par W C =
      W ≫ ((ρ_ (bObj Δ₁)).inv ≫ bObj Δ₁ ◁ C ≫ (bMu Δ₁ Δ₂).hom) := fun W => by
    change (λ_ _).inv ≫ (W ⊗ₘ C) ≫ (bMu Δ₁ Δ₂).hom = _
    rw [MonoidalCategory.tensorHom_def, unitors_inv_equal, Category.assoc,
      ← rightUnitor_inv_naturality_assoc]
  rw [hp, hp]
  exact h.comp _

/-- Putting a context `C` in parallel on the left preserves emulation. -/
theorem par_right {Δ₁ Δ₂ : PortBoundary} (C : loopOpenTheory.Obj Δ₁)
    {real ideal : loopOpenTheory.Obj Δ₂} (h : EmulatesΩ real ideal) :
    EmulatesΩ (loopOpenTheory.par C real) (loopOpenTheory.par C ideal) := by
  rw [← par_comm' real C, ← par_comm' ideal C]
  exact (h.par_left C).map _

/-- **Composition theorem for `wire`.** If each factor emulates its ideal, the wiring of the
factors emulates the wiring of the ideals. -/
theorem wire_compose {Δ₁ Γ Δ₂ : PortBoundary} {real₁ ideal₁ : loopOpenTheory.Obj (Δ₁.tensor Γ)}
    {real₂ ideal₂ : loopOpenTheory.Obj (Γ.swap.tensor Δ₂)} (h₁ : EmulatesΩ real₁ ideal₁)
    (h₂ : EmulatesΩ real₂ ideal₂) :
    EmulatesΩ (loopOpenTheory.wire real₁ real₂) (loopOpenTheory.wire ideal₁ ideal₂) :=
  (h₁.wire_left real₂).trans (wire_right ideal₁ h₂)

/-- **Composition theorem for `par`.** If each component emulates its ideal, the parallel
composition of the components emulates that of the ideals. -/
theorem par_compose {Δ₁ Δ₂ : PortBoundary} {real₁ ideal₁ : loopOpenTheory.Obj Δ₁}
    {real₂ ideal₂ : loopOpenTheory.Obj Δ₂} (h₁ : EmulatesΩ real₁ ideal₁)
    (h₂ : EmulatesΩ real₂ ideal₂) :
    EmulatesΩ (loopOpenTheory.par real₁ real₂) (loopOpenTheory.par ideal₁ ideal₂) :=
  (h₁.par_left real₂).trans (par_right ideal₁ h₂)

end EmulatesΩ

end CatCrypt.Crypto.UCLoopbackObservation
