/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCLoopbackOpenTheory
public import CatCryptCore.Quantum.QSysCatOpenTheory
public import CatCryptCore.Crypto.Party.Category
-- import all: unfolds the boundary equivalences `tensorComm` and `tensorAssoc`
import all PolyFun.Interaction.Interface

/-!
# Port plumbing by monoidal coherence

Wiring and port plumbing in the categories of reactive systems: monoidal coherence for the
structure maps, and a normal form for the morphisms given by functions of ports.

The categories `SysCat` (classical reactive systems), `QSysCat R` (quantum reactive systems),
their Int constructions `IntConstruction SysCat`, `IntConstruction (QSysCat R)` and the party
category `Party.Diag g` are symmetric monoidal categories through ordinary instances, so
Mathlib's `monoidal` tactic decides the equalities between composites of associators,
unitors and whiskerings of arbitrary morphisms, with braidings and other morphisms as atoms.
No registration is needed.

Port plumbing equalities whose two sides are built from `homOfFun` and `isoOfEquiv` (port
relabellings by concrete functions such as `Equiv.sumAssoc`, `swapFun` or the packet
equivalences of port boundaries) are not instances of coherence: their atoms are concrete
functions. The tactic `port_simp` rewrites such a composite to one morphism `homOfFun f`
(a pair `mkHom (homOfFun f) (homOfFun g)` in the Int construction), and `port_ext` closes the
resulting equality by extensionality of the functions and case analysis on sums.

## Main definitions

* `port_simp`, `port_simp [h₁, …]`: the normal form of composites of `homOfFun`,
  `isoOfEquiv`, structure maps and `mkHom` in `SysCat`, `QSysCat R` and their Int
  constructions.
* `port_ext`: closes `homOfFun f = homOfFun g` and `mkHom u v = mkHom u' v'` by `funext` and
  `port_cases`.
* `port_cases`: case analysis on every hypothesis whose type reduces to a sum, a dependent
  pair, `Empty` or `PEmpty`, recursively.
* `port_coherence`, `port_coherence [h₁, …]`: `monoidal`, else `port_simp` followed by
  `port_ext`.

## Main results

The theorems of the section `Examples` restate structural and port plumbing lemmas of
`UCLoopbackInt`, `UCLoopbackOpenTheory` and `QSysCatOpenTheory` and prove them by
`port_coherence`.
-/

@[expose] public section

set_option autoImplicit false

meta section

namespace CatCrypt.Tactics.PortCoherence

open Lean Meta Elab Tactic

/-- Whether the type `t` reduces to a sum, a dependent pair, `Empty` or `PEmpty`: the types
of ports that `port_cases` splits. -/
def isPortSplit (t : Expr) : MetaM Bool := do
  let t ← whnfD t
  let f := t.getAppFn
  return f.isConstOf ``Sum || f.isConstOf ``Sigma || f.isConstOf ``Empty ||
    f.isConstOf ``PEmpty

/-- Splits the goal `g` by `cases` on its hypotheses whose types reduce to a sum, a dependent
pair, `Empty` or `PEmpty`, recursively. -/
partial def portCasesGoal (g : MVarId) : MetaM (List MVarId) := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if ← isPortSplit d.type then
      let subs ← g.cases d.fvarId
      let mut out := []
      for s in subs do
        out := out ++ (← portCasesGoal s.mvarId)
      return out
  return [g]

/-- `port_cases` splits the main goal by case analysis on every hypothesis whose type reduces
to a sum, a dependent pair, `Empty` or `PEmpty` (a port of a tensor product of systems),
recursively. -/
syntax (name := portCasesStx) "port_cases" : tactic

/-- The elaborator of `port_cases`. -/
@[tactic portCasesStx] def evalPortCases : Tactic := fun _ => do
  let g ← getMainGoal
  replaceMainGoal (← portCasesGoal g)

end CatCrypt.Tactics.PortCoherence

end

namespace CatCrypt.Tactics.PortCoherence

open Lean Parser Tactic

/-- `port_simp` rewrites composites of morphisms given by functions of ports (`homOfFun`,
`isoOfEquiv`), structure maps and whiskerings in `SysCat` and `QSysCat R`, and morphisms
`mkHom` of their Int constructions, to a single `homOfFun` (or `mkHom` of two). `port_simp
[h₁, …]` adds rewrite rules, for instance the definitions of boundary maps to unfold. -/
syntax (name := portSimp) "port_simp" (" [" simpArg,* "]")? : tactic

macro_rules
  | `(tactic| port_simp) => `(tactic| port_simp [])
  | `(tactic| port_simp [$args,*]) =>
    `(tactic| simp only [
      CategoryTheory.IntConstruction.mkIso_hom, CategoryTheory.IntConstruction.mkIso_inv,
      CategoryTheory.IntConstruction.mkHom_whiskerRight,
      CategoryTheory.IntConstruction.whiskerLeft_mkHom,
      CategoryTheory.IntConstruction.associator_hom,
      CategoryTheory.IntConstruction.associator_inv,
      CategoryTheory.IntConstruction.leftUnitor_hom,
      CategoryTheory.IntConstruction.leftUnitor_inv,
      CategoryTheory.IntConstruction.rightUnitor_hom,
      CategoryTheory.IntConstruction.rightUnitor_inv,
      CategoryTheory.IntConstruction.tensorHom_mkHom,
      CategoryTheory.IntConstruction.mkHom_comp_mkHom,
      CategoryTheory.IntConstruction.id_eq_mkHom,
      CatCrypt.Crypto.UCTransparent.IntSys.braiding_hom,
      CatCrypt.Crypto.UCTransparent.IntSys.mkHom_tensorHom_mkHom,
      CatCrypt.Quantum.ReactiveUC.IntQSys.braiding_hom,
      CatCrypt.Quantum.ReactiveUC.IntQSys.mkHom_tensorHom_mkHom,
      CatCrypt.Crypto.UCTransparent.SysCat.id_eq_homOfFun,
      CatCrypt.Quantum.ReactiveUC.QSysCat.id_eq_homOfFun,
      CatCrypt.Crypto.UCTransparent.SysCat.swapRight_eq_homOfFun,
      CatCrypt.Crypto.UCTransparent.SysCat.isoOfEquiv_hom,
      CatCrypt.Crypto.UCTransparent.SysCat.isoOfEquiv_inv,
      CatCrypt.Crypto.UCTransparent.SysCat.associator_def,
      CatCrypt.Crypto.UCTransparent.SysCat.leftUnitor_def,
      CatCrypt.Crypto.UCTransparent.SysCat.rightUnitor_def,
      CatCrypt.Crypto.UCTransparent.SysCat.braiding_def,
      CatCrypt.Crypto.UCTransparent.SysCat.whiskerLeft_homOfFun,
      CatCrypt.Crypto.UCTransparent.SysCat.whiskerRight_homOfFun,
      CatCrypt.Crypto.UCTransparent.SysCat.homOfFun_tensorHom',
      CatCrypt.Crypto.UCTransparent.SysCat.homOfFun_comp,
      CatCrypt.Quantum.ReactiveUC.QSysCat.swapRight_eq_homOfFun,
      CatCrypt.Quantum.ReactiveUC.QSysCat.isoOfEquiv_hom,
      CatCrypt.Quantum.ReactiveUC.QSysCat.isoOfEquiv_inv,
      CatCrypt.Quantum.ReactiveUC.QSysCat.associator_def,
      CatCrypt.Quantum.ReactiveUC.QSysCat.leftUnitor_def,
      CatCrypt.Quantum.ReactiveUC.QSysCat.rightUnitor_def,
      CatCrypt.Quantum.ReactiveUC.QSysCat.braiding_def,
      CatCrypt.Quantum.ReactiveUC.QSysCat.whiskerLeft_homOfFun,
      CatCrypt.Quantum.ReactiveUC.QSysCat.whiskerRight_homOfFun,
      CatCrypt.Quantum.ReactiveUC.QSysCat.homOfFun_tensorHom',
      CatCrypt.Quantum.ReactiveUC.QSysCat.homOfFun_comp, $args,*])

/-- `port_ext` closes an equality `homOfFun f = homOfFun g` of `SysCat` or `QSysCat R`, or
`mkHom u v = mkHom u' v'` of their Int constructions with `u, v, u', v'` of that form, by
extensionality of the functions of ports and case analysis on sums and `Empty`. -/
syntax (name := portExt) "port_ext" : tactic

macro_rules
  | `(tactic| port_ext) =>
    `(tactic| first
      | with_reducible rfl
      | (refine congrArg₂ CategoryTheory.IntConstruction.mkHom ?_ ?_ <;> port_ext)
      | (refine congrArg _ ?_
         funext x
         port_cases <;> rfl))

/-- `port_coherence` closes a structural equality of a monoidal category by `monoidal`, and
otherwise a port plumbing equality in `SysCat`, `QSysCat R` or their Int constructions by
`port_simp` and `port_ext`. `port_coherence [h₁, …]` passes the rules `hᵢ` to `port_simp`. -/
syntax (name := portCoherence) "port_coherence" (" [" simpArg,* "]")? : tactic

macro_rules
  | `(tactic| port_coherence) => `(tactic| port_coherence [])
  | `(tactic| port_coherence [$args,*]) =>
    `(tactic| first | (monoidal; done) | (port_simp [$args,*]; port_ext))

end CatCrypt.Tactics.PortCoherence

/-! ## Examples -/

namespace CatCrypt.Tactics.PortCoherence.Examples

open CategoryTheory MonoidalCategory BraidedCategory

section Coherence

variable {C : Type*} [Category C] [MonoidalCategory C] [SymmetricCategory C]

/-- A structural equality with a morphism and a braiding as atoms, in any symmetric monoidal
category. -/
theorem whiskerLeft_braiding_unit (X Y Z : C) (f : Y ⟶ Z) :
    X ◁ (λ_ Y).inv ≫ X ◁ (𝟙_ C ◁ f) ≫ (α_ X (𝟙_ C) Z).inv ≫ (ρ_ X).hom ▷ Z ≫ (β_ X Z).hom =
      X ◁ f ≫ (β_ X Z).hom := by
  port_coherence

/-- The pentagon in `SysCat`. -/
theorem sysCat_pentagon (W X Y Z : CatCrypt.Crypto.UCTransparent.SysCat) :
    (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom =
      (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom := by
  port_coherence

/-- A structural equality with a braiding as atom in `QSysCat R`. -/
theorem qSysCat_unit_braiding {R : Type} [Fintype R]
    (X Y : CatCrypt.Quantum.ReactiveUC.QSysCat R) :
    (ρ_ (X ⊗ Y)).hom ≫ (β_ X Y).hom = (α_ X Y (𝟙_ _)).hom ≫ X ◁ (ρ_ Y).hom ≫ (β_ X Y).hom := by
  port_coherence

/-- An associativity equality with morphism atoms in the Int construction on `SysCat`. -/
theorem intSys_assoc_naturality
    {X X' Y Z : IntConstruction CatCrypt.Crypto.UCTransparent.SysCat} (f : X ⟶ X') :
    (α_ X Y Z).inv ≫ (f ▷ Y) ▷ Z = f ▷ (Y ⊗ Z) ≫ (α_ X' Y Z).inv := by
  port_coherence

/-- The triangle in the party category `Diag g`. -/
theorem diag_triangle [TracedCategory C] {Gen : C → C → Type*}
    {g : ∀ {X Y : C}, Gen X Y → (X ⟶ Y)}
    (X Y : CatCrypt.Crypto.Party.Diag g) :
    (α_ X (𝟙_ _) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y := by
  port_coherence

end Coherence

section Plumbing

open CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.SysCat

/-- `UCLoopbackInt.swapRight_eq_homOfFun`, restated. -/
theorem sys_swapRight_eq_homOfFun (X U V : SysCat) :
    swapRight X U V = homOfFun (X := (X ⊗ U) ⊗ V) (Y := (X ⊗ V) ⊗ U) swapFun := by
  unfold swapRight
  port_coherence

end Plumbing

section Boundary

open CatCrypt.Core CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.SysCat
open CatCrypt.Crypto.UCTransparent.IntSys CatCrypt.Crypto.UCOpenTheory
open CatCrypt.Crypto.UCLoopbackOpenTheory Interaction Interaction.Open

/-- `UCLoopbackOpenTheory.bMap_id`, restated. -/
theorem sys_bMap_id (Δ : PortBoundary) : bMap (PortBoundary.Hom.id Δ) = 𝟙 (bObj Δ) := by
  port_coherence [bMap, PortBoundary.Hom.id]

/-- `UCLoopbackOpenTheory.bMu_bMap`, restated. -/
theorem sys_bMu_bMap {Δ₁ Δ₂ Δ₁' Δ₂' : PortBoundary} (f₁ : PortBoundary.Hom Δ₁ Δ₁')
    (f₂ : PortBoundary.Hom Δ₂ Δ₂') :
    (bMu Δ₁ Δ₂).hom ≫ bMap (f₁.tensor f₂) = (bMap f₁ ⊗ₘ bMap f₂) ≫ (bMu Δ₁' Δ₂').hom := by
  port_coherence [bMu, bMap, PortBoundary.Hom.tensor]

/-- `UCLoopbackOpenTheory.bMap_comp`, restated. -/
theorem sys_bMap_comp {Δ₁ Δ₂ Δ₃ : PortBoundary} (g : PortBoundary.Hom Δ₂ Δ₃)
    (f : PortBoundary.Hom Δ₁ Δ₂) : bMap (PortBoundary.Hom.comp g f) = bMap f ≫ bMap g := by
  port_coherence [bMap, PortBoundary.Hom.comp]

/-- `UCLoopbackOpenTheory.bMu_assoc`, restated. -/
theorem sys_bMu_assoc (Δ₁ Δ₂ Δ₃ : PortBoundary) :
    (bMu Δ₁ Δ₂).hom ▷ bObj Δ₃ ≫ (bMu (Δ₁.tensor Δ₂) Δ₃).hom ≫
        bMap (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).toHom =
      (α_ _ _ _).hom ≫ bObj Δ₁ ◁ (bMu Δ₂ Δ₃).hom ≫ (bMu Δ₁ (Δ₂.tensor Δ₃)).hom := by
  port_coherence [bMu, bMap]

/-- `UCLoopbackOpenTheory.bMu_assoc_symm`, restated. -/
theorem sys_bMu_assoc_symm (Δ₁ Δ₂ Δ₃ : PortBoundary) :
    bObj Δ₁ ◁ (bMu Δ₂ Δ₃).hom ≫ (bMu Δ₁ (Δ₂.tensor Δ₃)).hom ≫
        bMap (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).symm.toHom =
      (α_ _ _ _).inv ≫ (bMu Δ₁ Δ₂).hom ▷ bObj Δ₃ ≫ (bMu (Δ₁.tensor Δ₂) Δ₃).hom := by
  port_coherence [bMu, bMap]

/-- `UCLoopbackOpenTheory.bMu_comm`, restated. -/
theorem sys_bMu_comm (Δ₁ Δ₂ : PortBoundary) :
    (bMu Δ₁ Δ₂).hom ≫ bMap (PortBoundary.Equiv.tensorComm Δ₁ Δ₂).toHom =
      (β_ _ _).hom ≫ (bMu Δ₂ Δ₁).hom := by
  port_coherence [bMu, bMap]

/-- `UCLoopbackOpenTheory.bMu_leftUnit`, restated. -/
theorem sys_bMu_leftUnit (Δ : PortBoundary) :
    bUnit.hom ▷ bObj Δ ≫ (bMu PortBoundary.empty Δ).hom ≫
        bMap (PortBoundary.Equiv.tensorEmptyLeft Δ).toHom = (λ_ (bObj Δ)).hom := by
  port_coherence [bMu, bMap, bUnit]

/-- `UCLoopbackOpenTheory.bMu_rightUnit`, restated. -/
theorem sys_bMu_rightUnit (Δ : PortBoundary) :
    bObj Δ ◁ bUnit.hom ≫ (bMu Δ PortBoundary.empty).hom ≫
        bMap (PortBoundary.Equiv.tensorEmptyRight Δ).toHom = (ρ_ (bObj Δ)).hom := by
  port_coherence [bMu, bMap, bUnit]

end Boundary

section QBoundary

open CatCrypt.Quantum.ReactiveUC CatCrypt.Quantum.ReactiveUC.QSysCat
open CatCrypt.Quantum.ReactiveUC.IntQSys CatCrypt.Quantum.ReactiveUC.QOpenTheory
open CatCrypt.Crypto.UCOpenTheory Interaction Interaction.Open

variable {R : Type} [Fintype R]

/-- `QSysCatOpenTheory.swapRight_eq_homOfFun`, restated. -/
theorem qsys_swapRight_eq_homOfFun (X U V : QSysCat R) :
    swapRight X U V = homOfFun (X := (X ⊗ U) ⊗ V) (Y := (X ⊗ V) ⊗ U) swapFun := by
  unfold swapRight
  port_coherence

/-- `QOpenTheory.bMap_id`, restated. -/
theorem qsys_bMap_id (Δ : PortBoundary) :
    bMap (R := R) (PortBoundary.Hom.id Δ) = 𝟙 (bObj R Δ) := by
  port_coherence [bMap, PortBoundary.Hom.id]

/-- `QOpenTheory.bMu_bMap`, restated. -/
theorem qsys_bMu_bMap {Δ₁ Δ₂ Δ₁' Δ₂' : PortBoundary} (f₁ : PortBoundary.Hom Δ₁ Δ₁')
    (f₂ : PortBoundary.Hom Δ₂ Δ₂') :
    (bMu R Δ₁ Δ₂).hom ≫ bMap (f₁.tensor f₂) = (bMap f₁ ⊗ₘ bMap f₂) ≫ (bMu R Δ₁' Δ₂').hom := by
  port_coherence [bMu, bMap, PortBoundary.Hom.tensor]

/-- `QOpenTheory.bMap_comp`, restated. -/
theorem qsys_bMap_comp {Δ₁ Δ₂ Δ₃ : PortBoundary} (g : PortBoundary.Hom Δ₂ Δ₃)
    (f : PortBoundary.Hom Δ₁ Δ₂) :
    bMap (R := R) (PortBoundary.Hom.comp g f) = bMap f ≫ bMap g := by
  port_coherence [bMap, PortBoundary.Hom.comp]

/-- `QOpenTheory.bMu_assoc`, restated. -/
theorem qsys_bMu_assoc (Δ₁ Δ₂ Δ₃ : PortBoundary) :
    (bMu R Δ₁ Δ₂).hom ▷ bObj R Δ₃ ≫ (bMu R (Δ₁.tensor Δ₂) Δ₃).hom ≫
        bMap (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).toHom =
      (α_ _ _ _).hom ≫ bObj R Δ₁ ◁ (bMu R Δ₂ Δ₃).hom ≫ (bMu R Δ₁ (Δ₂.tensor Δ₃)).hom := by
  port_coherence [bMu, bMap]

/-- `QOpenTheory.bMu_assoc_symm`, restated. -/
theorem qsys_bMu_assoc_symm (Δ₁ Δ₂ Δ₃ : PortBoundary) :
    bObj R Δ₁ ◁ (bMu R Δ₂ Δ₃).hom ≫ (bMu R Δ₁ (Δ₂.tensor Δ₃)).hom ≫
        bMap (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).symm.toHom =
      (α_ _ _ _).inv ≫ (bMu R Δ₁ Δ₂).hom ▷ bObj R Δ₃ ≫ (bMu R (Δ₁.tensor Δ₂) Δ₃).hom := by
  port_coherence [bMu, bMap]

/-- `QOpenTheory.bMu_comm`, restated. -/
theorem qsys_bMu_comm (Δ₁ Δ₂ : PortBoundary) :
    (bMu R Δ₁ Δ₂).hom ≫ bMap (PortBoundary.Equiv.tensorComm Δ₁ Δ₂).toHom =
      (β_ _ _).hom ≫ (bMu R Δ₂ Δ₁).hom := by
  port_coherence [bMu, bMap]

/-- `QOpenTheory.bMu_leftUnit`, restated. -/
theorem qsys_bMu_leftUnit (Δ : PortBoundary) :
    (bUnit R).hom ▷ bObj R Δ ≫ (bMu R PortBoundary.empty Δ).hom ≫
        bMap (PortBoundary.Equiv.tensorEmptyLeft Δ).toHom = (λ_ (bObj R Δ)).hom := by
  port_coherence [bMu, bMap, bUnit]

/-- `QOpenTheory.bMu_rightUnit`, restated. -/
theorem qsys_bMu_rightUnit (Δ : PortBoundary) :
    bObj R Δ ◁ (bUnit R).hom ≫ (bMu R Δ PortBoundary.empty).hom ≫
        bMap (PortBoundary.Equiv.tensorEmptyRight Δ).toHom = (ρ_ (bObj R Δ)).hom := by
  port_coherence [bMu, bMap, bUnit]

end QBoundary

end CatCrypt.Tactics.PortCoherence.Examples
