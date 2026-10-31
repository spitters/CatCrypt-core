/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QSysCat
public import CatCryptCore.ForMathlib.CategoryTheory.Monoidal.IntConstructionMonoidal
public import CatCryptCore.Crypto.UCLoopbackObservation
-- import all: unfolds the boundary equivalences `tensorComm` and `tensorAssoc`
import all PolyFun.Interaction.Interface

/-!
# The Int construction on quantum reactive systems as a PolyFun open theory

`IntConstruction (QSysCat R)` is the Int construction of Joyal, Street and Verity on the traced
symmetric monoidal category `QSysCat R` of port types and quantum reactive systems on the
register `R` modulo step equivalence (`QSysCat.tracedCategory`); it is compact closed
(`IntConstruction.instRigidCategory`). Composition in it is the trace of `QSysCat R` over the
shared negative component, the unbounded loopback `QRSys.loopbackω` in Selinger's order.

The Int construction carries a PolyFun `OpenTheory`, `QOpenTheory.qOpenTheory R`, that satisfies
`OpenTheory.HasPlugWireFactor` with equality of objects. A port boundary `Δ` is the object
`bObj Δ = (Δ.Out, Δ.In)` of packets, and a quantum open system on `Δ` is a morphism
`𝟙 ⟶ bObj Δ`: the class of a quantum reactive system on `R` that receives the packets of
`Δ.In` and emits the packets of `Δ.Out`. `map` composes with the morphism of a boundary
morphism, `par` is the tensor product, `wire` composes through names (the forwarding pairing
`cup`/`cap`), and `plug` is the evaluation `cap`.

Quantum UC emulation `EmulatesΩ` compares open systems through the bit boundary
`UCLoopbackObservation.bitBoundary`: a test of an open system on `Δ` is an open system on
`Δ.swap ⊗ bitBoundary`, the run wires the system with the test along `Δ`, and the observation
`obsBit` is the subinstrument on the register `R` of the first activation on the start packet
with the returned bit as outcome. Every test is composition with a morphism of the Int
construction (`runTest_eq`), so emulation is preserved by composition (`EmulatesΩ.comp`), and
the composition theorems for `map`, `par` and `wire` (the feedback of the open theory) follow
from the open-theory laws `wire_comm'` and `par_comm'`.

The development is the quantum counterpart of `UCLoopbackInt`, `UCLoopbackOpenTheory` and
`UCLoopbackObservation` for the classical category `SysCat`.

## Main definitions

* `QSysCat.fbIter`: the feedback of a port function, run with bounded fuel.
* `QSysCat.iface`, `QSysCat.sysHom`: interfaces and quantum systems in the Int construction.
* `IntQSys.cup`, `IntQSys.cap`, `IntQSys.nameEquiv`: the forwarding pairing and names.
* `QOpenTheory.bObj`, `QOpenTheory.bMap`, `QOpenTheory.bMu`: port boundaries as objects.
* `QOpenTheory.qOpenTheory`: the quantum open theory.
* `QOpenTheory.obsBit`, `QOpenTheory.runTest`, `QOpenTheory.EmulatesΩ`: quantum emulation.

## Main results

* `QSysCat.trace_homOfFun`: the trace of a stateless system with bounded feedback.
* `IntQSys.cup_cap_zigzag`, `IntQSys.cap_cup_zigzag`: the zig-zag laws.
* `QOpenTheory.qOpenTheory_hasPlugWireFactor`: the quantum open theory satisfies
  `HasPlugWireFactor`.
* `QOpenTheory.closed_mk_eq_iff`: equality of closed systems is step equivalence.
* `QOpenTheory.runTest_eq`: a test is composition with the morphism it names.
* `QOpenTheory.EmulatesΩ.comp`, `EmulatesΩ.map`: emulation is preserved by composition.
* `QOpenTheory.EmulatesΩ.wire_compose`, `QOpenTheory.EmulatesΩ.par_compose`: the composition
  theorems for wiring and parallel composition.

## References

* A. Joyal, R. Street, D. Verity, *Traced monoidal categories*, Math. Proc. Cambridge Philos.
  Soc. 119 (1996).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Quantum.ReactiveUC

open _root_.Quantum CategoryTheory MonoidalCategory BraidedCategory

namespace QSysCat

variable {R : Type} [Fintype R]

/-- The feedback of the port function `f` from `x` with `n` further passes along the wire: the
output it reaches, or `none` when the fuel runs out. -/
def fbIter {Q S U : Type} (f : Q ⊕ U → S ⊕ U) : ℕ → Q ⊕ U → Option S
  | 0, x => Sum.elim some (fun _ => none) (f x)
  | n + 1, x => Sum.elim some (fun u => fbIter f n (.inr u)) (f x)

/-- The unbounded activation of the stateless system of `f` reaches the output of `fbIter`. -/
theorem fbRunω_ofFun {Q S U : Type} (f : Q ⊕ U → S ⊕ U) :
    ∀ (n : ℕ) (x : Q ⊕ U) (r : S), fbIter f n x = some r →
      (QRSys.ofFun (R := R) f).fbRunω x () = SubInstrument.pure ((), r) := by
  intro n
  induction n with
  | zero =>
    intro x r h
    rw [QRSys.fbRunω_eq, QRSys.ofFun_step, SubInstrument.pure_bind]
    rcases hx : f x with o | u <;> simp_all [fbIter]
  | succ n ih =>
    intro x r h
    rw [QRSys.fbRunω_eq, QRSys.ofFun_step, SubInstrument.pure_bind]
    rcases hx : f x with o | u
    · simp_all [fbIter]
    · simp only [fbIter, hx, Sum.elim_inr] at h
      exact ih _ _ h

/-- **Trace of a stateless system.** When the feedback of the port function `f` ends from every
outer event, the trace of its system is the system of the function it computes. -/
theorem trace_homOfFun {X Y U : QSysCat R} (f : X.P ⊕ U.P → Y.P ⊕ U.P) (g : X.P → Y.P)
    (h : ∀ x, ∃ n, fbIter f n (.inl x) = some (g x)) :
    TracedCategory.trace U (homOfFun (X := X ⊗ U) (Y := Y ⊗ U) f) = homOfFun g := by
  refine Quotient.sound (QRSys.StepMap.stepEq (S := (QRSys.ofFun (R := R) f).loopbackω)
    (T := QRSys.ofFun g) (f := id) ⟨rfl, fun t e => ?_⟩)
  obtain ⟨n, hn⟩ := h e
  rw [QRSys.loopbackω_step, fbRunω_ofFun f n _ _ hn, SubInstrument.pure_bind]
  rfl

/-- Morphisms out of a port type without ports are equal: their systems have no events. -/
theorem hom_eq_of_isEmpty {X Y : QSysCat R} (hX : IsEmpty X.P) (a b : X ⟶ Y) : a = b := by
  induction a using Quotient.inductionOn with
  | h A =>
    induction b using Quotient.inductionOn with
    | h B =>
      exact Quotient.sound (QRSys.StepMap.stepEq (S := A.sys) (T := B.sys)
        (f := fun _ => B.sys.init) ⟨rfl, fun _ e => isEmptyElim e⟩)

/-- Unfolding lemma of the symmetry. -/
theorem braiding_def (X Y : QSysCat R) :
    β_ X Y = isoOfEquiv (X := X ⊗ Y) (Y := Y ⊗ X) (Equiv.sumComm X.P Y.P) :=
  rfl

/-- The tensor product of morphisms given by functions, in the monoidal notation. -/
theorem homOfFun_tensorHom' {X₁ Y₁ X₂ Y₂ : QSysCat R} (f : X₁.P → Y₁.P) (g : X₂.P → Y₂.P) :
    homOfFun f ⊗ₘ homOfFun g = homOfFun (X := X₁ ⊗ X₂) (Y := Y₁ ⊗ Y₂) (Sum.map f g) :=
  homOfFun_tensorHom f g

/-- The map of ports of `swapRight`, exchanging the last two summands. -/
def swapFun {A B C : Type} : (A ⊕ B) ⊕ C → (A ⊕ C) ⊕ B
  | .inl (.inl a) => .inl (.inl a)
  | .inl (.inr b) => .inr b
  | .inr c => .inl (.inr c)

/-- `swapRight X U V` is the morphism of the map of ports `swapFun`. -/
theorem swapRight_eq_homOfFun (X U V : QSysCat R) :
    swapRight X U V = homOfFun (X := (X ⊗ U) ⊗ V) (Y := (X ⊗ V) ⊗ U) swapFun := by
  change homOfFun _ ≫ X ◁ homOfFun _ ≫ homOfFun _ = _
  simp only [whiskerLeft_homOfFun, homOfFun_comp]
  congr 1
  funext p
  rcases p with (x | u) | v <;> rfl

/-- The interface `(E, O)` as an object of the Int construction on `QSysCat R`. -/
abbrev iface (R : Type) [Fintype R] (E O : Type) : IntConstruction (QSysCat R) :=
  ⟨⟨E⟩, ⟨O⟩⟩

/-- A quantum reactive system on `(E, O)` as a morphism `(E, O) ⟶ 𝟙` of the Int construction:
the class of the system on `E ⊕ Empty` and `Empty ⊕ O`. -/
noncomputable def sysHom {E O : Type} (A : QRSys.Obj R E O) :
    iface R E O ⟶ 𝟙_ (IntConstruction (QSysCat R)) :=
  ⟨(⟦A.mapPorts (Sum.elim id Empty.elim) Sum.inr⟧ : (⟨E ⊕ Empty⟩ : QSysCat R) ⟶ ⟨Empty ⊕ O⟩)⟩

end QSysCat

/-! ## Forwarding pairings in the Int construction -/

namespace IntQSys

open QSysCat IntConstruction

variable {R : Type} [Fintype R]

/-- The dual `(X⁻, X⁺)` of `X`, the object `IntConstruction.dual X` unfolded. -/
abbrev dualObj (X : IntConstruction (QSysCat R)) : IntConstruction (QSysCat R) :=
  ⟨X.neg, X.pos⟩

/-- The forwarding system `𝟙 ⟶ dualObj X ⊗ X`: a packet received on one side is emitted on the
other. -/
noncomputable def cup (X : IntConstruction (QSysCat R)) :
    𝟙_ (IntConstruction (QSysCat R)) ⟶ dualObj X ⊗ X :=
  ⟨homOfFun fun x => match x with
      | .inr (.inl p) => .inl (.inr p)
      | .inr (.inr n) => .inl (.inl n)⟩

/-- The forwarding system `X ⊗ dualObj X ⟶ 𝟙`: a packet emitted on one side is received on the
other. -/
noncomputable def cap (X : IntConstruction (QSysCat R)) :
    X ⊗ dualObj X ⟶ 𝟙_ (IntConstruction (QSysCat R)) :=
  ⟨homOfFun fun x => match x with
      | .inl (.inl p) => .inr (.inr p)
      | .inl (.inr n) => .inr (.inl n)⟩

/-- First zig-zag law of `cup` and `cap`. -/
theorem cup_cap_zigzag (X : IntConstruction (QSysCat R)) :
    X ◁ cup X ≫ (α_ X (dualObj X) X).inv ≫ cap X ▷ X = (ρ_ X).hom ≫ (λ_ X).inv := by
  apply IntConstruction.hom_ext
  rw [IntConstruction.comp_hom]
  simp only [IntConstruction.compKernel, IntConstruction.mkHom_comp_hom,
    IntConstruction.associator_inv, IntConstruction.rightUnitor_hom,
    IntConstruction.leftUnitor_inv, IntConstruction.mkHom_comp_mkHom,
    IntConstruction.mkHom_hom, IntConstruction.whiskerLeft_hom',
    IntConstruction.whiskerRight_hom', cup, cap, tensorμ, swapRight_eq_homOfFun,
    associator_def, leftUnitor_def, rightUnitor_def, braiding_def, isoOfEquiv_hom,
    isoOfEquiv_inv, whiskerLeft_homOfFun, whiskerRight_homOfFun, homOfFun_tensorHom',
    id_eq_homOfFun, homOfFun_comp]
  refine trace_homOfFun _ _ ?_
  rintro ((p | e) | (e | n))
  exacts [⟨3, rfl⟩, Empty.elim e, Empty.elim e, ⟨3, rfl⟩]

/-- Second zig-zag law of `cup` and `cap`. -/
theorem cap_cup_zigzag (X : IntConstruction (QSysCat R)) :
    cup X ▷ dualObj X ≫ (α_ (dualObj X) X (dualObj X)).hom ≫ dualObj X ◁ cap X =
      (λ_ (dualObj X)).hom ≫ (ρ_ (dualObj X)).inv := by
  apply IntConstruction.hom_ext
  rw [IntConstruction.comp_hom]
  simp only [IntConstruction.compKernel, IntConstruction.mkHom_comp_hom,
    IntConstruction.associator_hom, IntConstruction.rightUnitor_inv,
    IntConstruction.leftUnitor_hom, IntConstruction.mkHom_comp_mkHom,
    IntConstruction.mkHom_hom, IntConstruction.whiskerLeft_hom',
    IntConstruction.whiskerRight_hom', cup, cap, tensorμ, swapRight_eq_homOfFun,
    associator_def, leftUnitor_def, rightUnitor_def, braiding_def, isoOfEquiv_hom,
    isoOfEquiv_inv, whiskerLeft_homOfFun, whiskerRight_homOfFun, homOfFun_tensorHom',
    id_eq_homOfFun, homOfFun_comp]
  refine trace_homOfFun _ _ ?_
  rintro ((e | n) | (p | e))
  exacts [Empty.elim e, ⟨3, rfl⟩, ⟨3, rfl⟩, Empty.elim e]

/-- The forwarding systems `cup` and `cap` form an exact pairing of `dualObj X` with `X`. -/
@[instance_reducible]
noncomputable def cupCapPairing (X : IntConstruction (QSysCat R)) :
    ExactPairing (dualObj X) X where
  coevaluation' := cup X
  evaluation' := cap X
  coevaluation_evaluation' := cup_cap_zigzag X
  evaluation_coevaluation' := cap_cup_zigzag X

/-- Unfolding lemma of the symmetry of the Int construction. -/
theorem braiding_hom (X Y : IntConstruction (QSysCat R)) :
    (β_ X Y).hom = IntConstruction.mkHom (β_ X.pos Y.pos).hom (β_ X.neg Y.neg).inv :=
  rfl

/-- The forwarding system of the dual, followed by the symmetry, is the forwarding system. -/
theorem cup_dual_braiding (X : IntConstruction (QSysCat R)) :
    cup (dualObj X) ≫ (β_ X (dualObj X)).hom = cup X := by
  apply IntConstruction.hom_ext
  rw [IntConstruction.comp_hom]
  simp only [IntConstruction.compKernel, cup, braiding_hom, swapRight_eq_homOfFun, braiding_def,
    isoOfEquiv_hom, isoOfEquiv_inv, whiskerRight_homOfFun, homOfFun_tensorHom',
    IntConstruction.mkHom_hom, homOfFun_comp]
  refine trace_homOfFun _ _ ?_
  rintro (e | (p | n))
  exacts [Empty.elim e, ⟨1, rfl⟩, ⟨1, rfl⟩]

/-- Morphisms `G ⟶ B` and their names `𝟙 ⟶ dualObj G ⊗ B`, by the pairing of `cup` and `cap`. -/
noncomputable def nameEquiv (G B : IntConstruction (QSysCat R)) :
    (G ⟶ B) ≃ (𝟙_ (IntConstruction (QSysCat R)) ⟶ dualObj G ⊗ B) :=
  ((ρ_ G).homCongr (Iso.refl B)).symm.trans
    (@tensorLeftHomEquiv _ _ _ (𝟙_ _) (dualObj G) G B (cupCapPairing G))

/-- The name of `h` is the forwarding system followed by `h`. -/
theorem nameEquiv_apply {G B : IntConstruction (QSysCat R)} (h : G ⟶ B) :
    nameEquiv G B h = cup G ≫ dualObj G ◁ h := by
  dsimp only [nameEquiv, tensorLeftHomEquiv, Iso.homCongr, Equiv.trans_apply,
    Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
  monoidal

/-- Naming commutes with composition on the right. -/
theorem nameEquiv_comp {G B B' : IntConstruction (QSysCat R)} (h : G ⟶ B) (k : B ⟶ B') :
    nameEquiv G B' (h ≫ k) = nameEquiv G B h ≫ dualObj G ◁ k := by
  simp only [nameEquiv_apply, MonoidalCategory.whiskerLeft_comp, Category.assoc]

/-- Reading a name commutes with composition on the right. -/
theorem nameEquiv_symm_comp {G B B' : IntConstruction (QSysCat R)}
    (V : 𝟙_ (IntConstruction (QSysCat R)) ⟶ dualObj G ⊗ B) (k : B ⟶ B') :
    (nameEquiv G B').symm (V ≫ dualObj G ◁ k) = (nameEquiv G B).symm V ≫ k := by
  rw [Equiv.symm_apply_eq, nameEquiv_comp, Equiv.apply_symm_apply]

/-- Reading a name commutes with composition on the right, with a composite name. -/
theorem nameEquiv_symm_comp_assoc {G B B' Z : IntConstruction (QSysCat R)}
    (V : 𝟙_ (IntConstruction (QSysCat R)) ⟶ Z) (V' : Z ⟶ dualObj G ⊗ B) (k : B ⟶ B') :
    (nameEquiv G B').symm (V ≫ V' ≫ dualObj G ◁ k) = (nameEquiv G B).symm (V ≫ V') ≫ k := by
  rw [← Category.assoc, nameEquiv_symm_comp]

/-- The tensor product of two morphisms of the form `mkHom`, in the monoidal notation. -/
theorem mkHom_tensorHom_mkHom {X₁ Y₁ X₂ Y₂ : IntConstruction (QSysCat R)}
    (u : X₁.pos ⟶ Y₁.pos) (v : Y₁.neg ⟶ X₁.neg) (u' : X₂.pos ⟶ Y₂.pos)
    (v' : Y₂.neg ⟶ X₂.neg) :
    IntConstruction.mkHom u v ⊗ₘ IntConstruction.mkHom u' v' =
      IntConstruction.mkHom (X := X₁ ⊗ X₂) (Y := Y₁ ⊗ Y₂) (u ⊗ₘ u') (v ⊗ₘ v') :=
  IntConstruction.tensorHom_mkHom u v u' v'

end IntQSys

/-! ## Port boundaries as objects of the Int construction -/

namespace QOpenTheory

open QSysCat IntQSys
open CatCrypt.Crypto.UCOpenTheory CatCrypt.Crypto.UCLoopbackOpenTheory
open Interaction Interaction.Open

variable {R : Type} [Fintype R]

/-- The object of the port boundary `Δ`: positive component the packets of `Δ.Out`, negative
component the packets of `Δ.In`. -/
abbrev bObj (R : Type) [Fintype R] (Δ : PortBoundary) : IntConstruction (QSysCat R) :=
  ⟨⟨Interface.Packet Δ.Out⟩, ⟨Interface.Packet Δ.In⟩⟩

/-- The morphism of a boundary morphism: outputs translated forward, inputs backward. -/
noncomputable def bMap {Δ₁ Δ₂ : PortBoundary} (f : PortBoundary.Hom Δ₁ Δ₂) :
    bObj R Δ₁ ⟶ bObj R Δ₂ :=
  IntConstruction.mkHom (homOfFun (Interface.Hom.mapPacket f.onOut))
    (homOfFun (Interface.Hom.mapPacket f.onIn))

/-- The object of a tensor boundary is the tensor product of the objects. -/
noncomputable def bMu (R : Type) [Fintype R] (Δ₁ Δ₂ : PortBoundary) :
    bObj R Δ₁ ⊗ bObj R Δ₂ ≅ bObj R (Δ₁.tensor Δ₂) :=
  IntConstruction.mkIso (isoOfEquiv (packetSumEquiv _ _)) (isoOfEquiv (packetSumEquiv _ _))

/-- The object of the empty boundary is the unit. -/
noncomputable def bUnit (R : Type) [Fintype R] :
    𝟙_ (IntConstruction (QSysCat R)) ≅ bObj R PortBoundary.empty :=
  IntConstruction.mkIso (isoOfEquiv (Equiv.equivEmpty _).symm)
    (isoOfEquiv (Equiv.equivEmpty _).symm)

/-- The morphism of the identity boundary morphism is the identity. -/
theorem bMap_id (Δ : PortBoundary) : bMap (R := R) (PortBoundary.Hom.id Δ) = 𝟙 (bObj R Δ) := by
  simp only [bMap, PortBoundary.Hom.id, Interface.Hom.mapPacket_id, IntConstruction.id_eq_mkHom]
  rfl

/-- The morphism of a composite boundary morphism is the composite. -/
theorem bMap_comp {Δ₁ Δ₂ Δ₃ : PortBoundary} (g : PortBoundary.Hom Δ₂ Δ₃)
    (f : PortBoundary.Hom Δ₁ Δ₂) :
    bMap (R := R) (PortBoundary.Hom.comp g f) = bMap f ≫ bMap g := by
  simp only [bMap, PortBoundary.Hom.comp, IntConstruction.mkHom_comp_mkHom, homOfFun_comp,
    Interface.Hom.mapPacket_comp]

/-- `bMu` is natural in the two boundaries. -/
theorem bMu_bMap {Δ₁ Δ₂ Δ₁' Δ₂' : PortBoundary} (f₁ : PortBoundary.Hom Δ₁ Δ₁')
    (f₂ : PortBoundary.Hom Δ₂ Δ₂') :
    (bMu R Δ₁ Δ₂).hom ≫ bMap (f₁.tensor f₂) = (bMap f₁ ⊗ₘ bMap f₂) ≫ (bMu R Δ₁' Δ₂').hom := by
  simp only [bMu, bMap, IntConstruction.mkIso_hom, mkHom_tensorHom_mkHom,
    IntConstruction.mkHom_comp_mkHom, isoOfEquiv_hom, isoOfEquiv_inv, homOfFun_tensorHom',
    homOfFun_comp, PortBoundary.Hom.tensor]
  congr 2 <;> funext x
  · exact mapPacket_sum_insum _ _ x
  · exact (unsum_mapPacket_sum _ _ x)

/-- `bMu` and the associativity of boundaries. -/
theorem bMu_assoc (Δ₁ Δ₂ Δ₃ : PortBoundary) :
    (bMu R Δ₁ Δ₂).hom ▷ bObj R Δ₃ ≫ (bMu R (Δ₁.tensor Δ₂) Δ₃).hom ≫
        bMap (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).toHom =
      (α_ _ _ _).hom ≫ bObj R Δ₁ ◁ (bMu R Δ₂ Δ₃).hom ≫ (bMu R Δ₁ (Δ₂.tensor Δ₃)).hom := by
  simp only [bMu, bMap, IntConstruction.mkIso_hom, IntConstruction.mkHom_whiskerRight,
    IntConstruction.whiskerLeft_mkHom, IntConstruction.associator_hom,
    IntConstruction.mkHom_comp_mkHom, isoOfEquiv_hom, isoOfEquiv_inv, associator_def,
    whiskerLeft_homOfFun, whiskerRight_homOfFun, homOfFun_comp]
  congr 2 <;> funext x
  · rcases x with ((⟨a, b⟩ | ⟨a, b⟩) | ⟨a, b⟩) <;> rfl
  · rcases x with ⟨a | a | a, b⟩ <;> rfl

/-- `bMu` and the inverse associativity of boundaries. -/
theorem bMu_assoc_symm (Δ₁ Δ₂ Δ₃ : PortBoundary) :
    bObj R Δ₁ ◁ (bMu R Δ₂ Δ₃).hom ≫ (bMu R Δ₁ (Δ₂.tensor Δ₃)).hom ≫
        bMap (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).symm.toHom =
      (α_ _ _ _).inv ≫ (bMu R Δ₁ Δ₂).hom ▷ bObj R Δ₃ ≫ (bMu R (Δ₁.tensor Δ₂) Δ₃).hom := by
  simp only [bMu, bMap, IntConstruction.mkIso_hom, IntConstruction.mkHom_whiskerRight,
    IntConstruction.whiskerLeft_mkHom, IntConstruction.associator_inv,
    IntConstruction.mkHom_comp_mkHom, isoOfEquiv_hom, isoOfEquiv_inv, associator_def,
    whiskerLeft_homOfFun, whiskerRight_homOfFun, homOfFun_comp]
  congr 2 <;> funext x
  · rcases x with (⟨a, b⟩ | (⟨a, b⟩ | ⟨a, b⟩)) <;> rfl
  · rcases x with ⟨(a | a) | a, b⟩ <;> rfl

/-- `bMu` and the symmetry of boundaries. -/
theorem bMu_comm (Δ₁ Δ₂ : PortBoundary) :
    (bMu R Δ₁ Δ₂).hom ≫ bMap (PortBoundary.Equiv.tensorComm Δ₁ Δ₂).toHom =
      (β_ _ _).hom ≫ (bMu R Δ₂ Δ₁).hom := by
  simp only [bMu, bMap, braiding_hom, IntConstruction.mkIso_hom,
    IntConstruction.mkHom_comp_mkHom, isoOfEquiv_hom, isoOfEquiv_inv, braiding_def,
    homOfFun_comp]
  congr 2 <;> funext x
  · rcases x with ⟨a, b⟩ | ⟨a, b⟩ <;> rfl
  · rcases x with ⟨a | a, b⟩ <;> rfl

/-- `bMu` and the left unit of boundaries. -/
theorem bMu_leftUnit (Δ : PortBoundary) :
    (bUnit R).hom ▷ bObj R Δ ≫ (bMu R PortBoundary.empty Δ).hom ≫
        bMap (PortBoundary.Equiv.tensorEmptyLeft Δ).toHom = (λ_ (bObj R Δ)).hom := by
  simp only [bMu, bMap, bUnit, IntConstruction.mkIso_hom, IntConstruction.mkHom_whiskerRight,
    IntConstruction.leftUnitor_hom, IntConstruction.mkHom_comp_mkHom, isoOfEquiv_hom,
    isoOfEquiv_inv, leftUnitor_def, whiskerRight_homOfFun, homOfFun_comp]
  congr 2
  funext x
  rcases x with e | ⟨a, b⟩
  · exact Empty.elim e
  · rfl

/-- `bMu` and the right unit of boundaries. -/
theorem bMu_rightUnit (Δ : PortBoundary) :
    bObj R Δ ◁ (bUnit R).hom ≫ (bMu R Δ PortBoundary.empty).hom ≫
        bMap (PortBoundary.Equiv.tensorEmptyRight Δ).toHom = (ρ_ (bObj R Δ)).hom := by
  simp only [bMu, bMap, bUnit, IntConstruction.mkIso_hom, IntConstruction.whiskerLeft_mkHom,
    IntConstruction.rightUnitor_hom, IntConstruction.mkHom_comp_mkHom, isoOfEquiv_hom,
    isoOfEquiv_inv, rightUnitor_def, whiskerLeft_homOfFun, homOfFun_comp]
  congr 2
  funext x
  rcases x with ⟨a, b⟩ | e
  · rfl
  · exact Empty.elim e

/-- `bMu` is natural in the two boundaries, read through its inverse. -/
theorem bMap_bMu_inv {Δ₁ Δ₂ Δ₁' Δ₂' : PortBoundary} (f₁ : PortBoundary.Hom Δ₁ Δ₁')
    (f₂ : PortBoundary.Hom Δ₂ Δ₂') :
    bMap (f₁.tensor f₂) ≫ (bMu R Δ₁' Δ₂').inv = (bMu R Δ₁ Δ₂).inv ≫ (bMap f₁ ⊗ₘ bMap f₂) := by
  rw [Iso.comp_inv_eq, Category.assoc, ← bMu_bMap, Iso.inv_hom_id_assoc]

/-- `nameEquiv_symm_comp_assoc` at the object of a boundary, whose dual is the object of the
swapped boundary. -/
theorem nameEquiv_symm_bObj {Γ : PortBoundary} {B B' Z : IntConstruction (QSysCat R)}
    (V : 𝟙_ (IntConstruction (QSysCat R)) ⟶ Z) (V' : Z ⟶ bObj R Γ.swap ⊗ B) (k : B ⟶ B') :
    (nameEquiv (bObj R Γ) B').symm (V ≫ V' ≫ bObj R Γ.swap ◁ k) =
      (nameEquiv (bObj R Γ) B).symm (V ≫ V') ≫ k :=
  nameEquiv_symm_comp_assoc (G := bObj R Γ) (B := B) (B' := B') V V' k

/-- `nameEquiv_comp` at the object of a boundary. -/
theorem nameEquiv_comp_bObj {Γ : PortBoundary} {B B' : IntConstruction (QSysCat R)}
    (h : bObj R Γ ⟶ B) (k : B ⟶ B') :
    nameEquiv (bObj R Γ) B h ≫ bObj R Γ.swap ◁ k = nameEquiv (bObj R Γ) B' (h ≫ k) :=
  (nameEquiv_comp (G := bObj R Γ) h k).symm

/-- `cup_dual_braiding` at the object of a boundary. -/
theorem cup_bObj_swap (Γ : PortBoundary) :
    cup (bObj R Γ.swap) ≫ (β_ (bObj R Γ) (bObj R Γ.swap)).hom = cup (bObj R Γ) :=
  cup_dual_braiding (bObj R Γ)

/-! ## The open theory -/

/-- The wiring of `V₁ : 𝟙 ⟶ A ⊗ G` with `V₂ : 𝟙 ⟶ dualObj G ⊗ B`: `V₁` followed on `G` by the
morphism `G ⟶ B` that `V₂` names. -/
noncomputable def wireHom {A G B : IntConstruction (QSysCat R)}
    (V₁ : 𝟙_ (IntConstruction (QSysCat R)) ⟶ A ⊗ G)
    (V₂ : 𝟙_ (IntConstruction (QSysCat R)) ⟶ dualObj G ⊗ B) :
    𝟙_ (IntConstruction (QSysCat R)) ⟶ A ⊗ B :=
  V₁ ≫ A ◁ (nameEquiv G B).symm V₂

/-- The Int construction on quantum reactive systems as a PolyFun open theory: a quantum open
system on `Δ` is a morphism `𝟙 ⟶ bObj R Δ`, `map` composes with `bMap`, `par` is the tensor
product, `wire` composes through names and `plug` is the evaluation `cap`. -/
noncomputable abbrev qOpenTheory (R : Type) [Fintype R] : OpenTheory where
  Obj Δ := 𝟙_ (IntConstruction (QSysCat R)) ⟶ bObj R Δ
  map f W := W ≫ bMap f
  par {Δ₁ Δ₂} W₁ W₂ := (λ_ _).inv ≫ (W₁ ⊗ₘ W₂) ≫ (bMu R Δ₁ Δ₂).hom
  wire {Δ₁ Γ Δ₂} W₁ W₂ :=
    wireHom (G := bObj R Γ) (W₁ ≫ (bMu R Δ₁ Γ).inv) (W₂ ≫ (bMu R Γ.swap Δ₂).inv) ≫
      (bMu R Δ₁ Δ₂).hom
  plug {Δ} W K := (λ_ _).inv ≫ (W ⊗ₘ K) ≫ cap (bObj R Δ) ≫ (bUnit R).hom

/-- The unit of the open theory: the isomorphism `𝟙 ≅ bObj R empty`. -/
noncomputable instance : OpenTheory.HasUnit (qOpenTheory R) :=
  ⟨(bUnit R).hom⟩

/-- The identity wire on `Γ`: the name of the identity of `bObj R Γ`. -/
noncomputable instance : OpenTheory.HasIdWire (qOpenTheory R) :=
  ⟨fun Γ => nameEquiv (bObj R Γ) (bObj R Γ) (𝟙 _) ≫ (bMu R Γ.swap Γ).hom⟩

/-- A closed system has no events: `𝟙 ⟶ bObj R empty` has one element. -/
theorem closed_eq (a b : (qOpenTheory R).Obj PortBoundary.empty) : a = b :=
  IntConstruction.hom_ext (hom_eq_of_isEmpty ⟨fun x => by
    rcases x with e | p
    · exact Empty.elim e
    · exact noEv p⟩ _ _)

/-- The open theory is lawful: `map` is functorial, `par`, `wire`, `plug` are natural. -/
instance qOpenTheory_isLawful : OpenTheory.IsLawful (qOpenTheory R) where
  map_id W := by
    dsimp only
    rw [bMap_id, Category.comp_id]
  map_comp g f W := by
    dsimp only
    rw [bMap_comp, Category.assoc]
  map_par f₁ f₂ W₁ W₂ := by
    dsimp only
    rw [← MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.assoc, bMu_bMap]
  map_wire f₁ f₂ W₁ W₂ := by
    dsimp only
    simp only [wireHom, Category.assoc, bMu_bMap, bMap_bMu_inv, bMap_id,
      MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom]
    rw [nameEquiv_symm_bObj]
    simp only [MonoidalCategory.whiskerLeft_comp, MonoidalCategory.tensorHom_def,
      MonoidalCategory.whisker_exchange_assoc, Category.assoc]
  map_plug f W K := closed_eq _ _

/-- Associativity of `par`. -/
theorem par_assoc' {Δ₁ Δ₂ Δ₃ : PortBoundary} (W₁ : (qOpenTheory R).Obj Δ₁)
    (W₂ : (qOpenTheory R).Obj Δ₂) (W₃ : (qOpenTheory R).Obj Δ₃) :
    (qOpenTheory R).map (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).toHom
        ((qOpenTheory R).par ((qOpenTheory R).par W₁ W₂) W₃) =
      (qOpenTheory R).par W₁ ((qOpenTheory R).par W₂ W₃) := by
  dsimp only
  calc _ = (λ_ _).inv ≫ (((λ_ _).inv ≫ (W₁ ⊗ₘ W₂)) ⊗ₘ W₃) ≫
        ((bMu R Δ₁ Δ₂).hom ▷ bObj R Δ₃ ≫ (bMu R (Δ₁.tensor Δ₂) Δ₃).hom ≫
          bMap (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).toHom) := by monoidal
    _ = (λ_ _).inv ≫ (((λ_ _).inv ≫ (W₁ ⊗ₘ W₂)) ⊗ₘ W₃) ≫
        ((α_ _ _ _).hom ≫ bObj R Δ₁ ◁ (bMu R Δ₂ Δ₃).hom ≫ (bMu R Δ₁ (Δ₂.tensor Δ₃)).hom) := by
      rw [bMu_assoc]
    _ = _ := by monoidal

/-- Commutativity of `par`. -/
theorem par_comm' {Δ₁ Δ₂ : PortBoundary} (W₁ : (qOpenTheory R).Obj Δ₁)
    (W₂ : (qOpenTheory R).Obj Δ₂) :
    (qOpenTheory R).map (PortBoundary.Equiv.tensorComm Δ₁ Δ₂).toHom
        ((qOpenTheory R).par W₁ W₂) =
      (qOpenTheory R).par W₂ W₁ := by
  dsimp only
  rw [Category.assoc, Category.assoc, bMu_comm, BraidedCategory.braiding_naturality_assoc,
    braiding_tensorUnit_left, Category.assoc, Iso.inv_hom_id_assoc, ← unitors_inv_equal]

/-- Left unit law of `par`. -/
theorem par_leftUnit' {Δ : PortBoundary} (W : (qOpenTheory R).Obj Δ) :
    (qOpenTheory R).map (PortBoundary.Equiv.tensorEmptyLeft Δ).toHom
      ((qOpenTheory R).par (OpenTheory.HasUnit.unit (T := qOpenTheory R)) W) = W := by
  change ((λ_ _).inv ≫ ((bUnit R).hom ⊗ₘ W) ≫ (bMu R _ _).hom) ≫ bMap _ = W
  rw [MonoidalCategory.tensorHom_def', Category.assoc, Category.assoc, Category.assoc,
    bMu_leftUnit, MonoidalCategory.leftUnitor_naturality, Iso.inv_hom_id_assoc]

/-- Right unit law of `par`. -/
theorem par_rightUnit' {Δ : PortBoundary} (W : (qOpenTheory R).Obj Δ) :
    (qOpenTheory R).map (PortBoundary.Equiv.tensorEmptyRight Δ).toHom
      ((qOpenTheory R).par W (OpenTheory.HasUnit.unit (T := qOpenTheory R))) = W := by
  change ((λ_ _).inv ≫ (W ⊗ₘ (bUnit R).hom) ≫ (bMu R _ _).hom) ≫ bMap _ = W
  rw [MonoidalCategory.tensorHom_def, Category.assoc, Category.assoc, Category.assoc,
    bMu_rightUnit, MonoidalCategory.rightUnitor_naturality, unitors_inv_equal,
    Iso.inv_hom_id_assoc]

/-- The open theory satisfies the symmetric monoidal laws of `par` with equality. -/
noncomputable instance qOpenTheory_isMonoidal : OpenTheory.IsMonoidal (qOpenTheory R) where
  toIsLawful := inferInstance
  toHasUnit := inferInstance
  par_assoc := par_assoc'
  par_comm := par_comm'
  par_leftUnit := par_leftUnit'
  par_rightUnit := par_rightUnit'

/-- Every open system on a tensor boundary is `V ≫ bMu.hom` for a morphism `V` into the
tensor product. -/
theorem exists_bMu {Δ₁ Δ₂ : PortBoundary} (W : (qOpenTheory R).Obj (Δ₁.tensor Δ₂)) :
    ∃ V : 𝟙_ (IntConstruction (QSysCat R)) ⟶ bObj R Δ₁ ⊗ bObj R Δ₂,
      W = V ≫ (bMu R Δ₁ Δ₂).hom :=
  ⟨W ≫ (bMu R Δ₁ Δ₂).inv, by simp⟩

/-- Associativity of `wire`. -/
theorem wire_assoc' {Δ₁ Γ₁ Γ₂ Δ₃ : PortBoundary} (W₁ : (qOpenTheory R).Obj (Δ₁.tensor Γ₁))
    (W₂ : (qOpenTheory R).Obj (Γ₁.swap.tensor Γ₂))
    (W₃ : (qOpenTheory R).Obj (Γ₂.swap.tensor Δ₃)) :
    (qOpenTheory R).wire ((qOpenTheory R).wire W₁ W₂) W₃ =
      (qOpenTheory R).wire W₁ ((qOpenTheory R).wire W₂ W₃) := by
  dsimp only
  simp only [wireHom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [nameEquiv_symm_bObj, MonoidalCategory.whiskerLeft_comp, Category.assoc]

/-- Superposition of `par` and `wire`. -/
theorem wire_par_superpose' {Δ₁ Δ₂ Γ Δ₃ : PortBoundary} (W₁ : (qOpenTheory R).Obj Δ₁)
    (W₂ : (qOpenTheory R).Obj (Δ₂.tensor Γ)) (W₃ : (qOpenTheory R).Obj (Γ.swap.tensor Δ₃)) :
    (qOpenTheory R).wire
        ((qOpenTheory R).map (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Γ).symm.toHom
          ((qOpenTheory R).par W₁ W₂)) W₃ =
      (qOpenTheory R).map (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).symm.toHom
        ((qOpenTheory R).par W₁ ((qOpenTheory R).wire W₂ W₃)) := by
  obtain ⟨V₂, rfl⟩ := exists_bMu W₂
  dsimp only
  simp only [wireHom, Category.assoc, Iso.hom_inv_id_assoc]
  generalize (nameEquiv (bObj R Γ) (bObj R Δ₃)).symm (W₃ ≫ (bMu R Γ.swap Δ₃).inv) = h
  calc _ = (λ_ _).inv ≫ (W₁ ⊗ₘ V₂) ≫
        (bObj R Δ₁ ◁ (bMu R Δ₂ Γ).hom ≫ (bMu R Δ₁ (Δ₂.tensor Γ)).hom ≫
          bMap (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Γ).symm.toHom) ≫
        (bMu R (Δ₁.tensor Δ₂) Γ).inv ≫ bObj R (Δ₁.tensor Δ₂) ◁ h ≫
          (bMu R (Δ₁.tensor Δ₂) Δ₃).hom := by monoidal
    _ = (λ_ _).inv ≫ (W₁ ⊗ₘ V₂) ≫ (α_ _ _ _).inv ≫
        ((bMu R Δ₁ Δ₂).hom ▷ bObj R Γ ≫ bObj R (Δ₁.tensor Δ₂) ◁ h) ≫
          (bMu R (Δ₁.tensor Δ₂) Δ₃).hom := by
      rw [bMu_assoc_symm]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = (λ_ _).inv ≫ (W₁ ⊗ₘ V₂) ≫ (α_ _ _ _).inv ≫
        ((bObj R Δ₁ ⊗ bObj R Δ₂) ◁ h ≫ (bMu R Δ₁ Δ₂).hom ▷ bObj R Δ₃) ≫
          (bMu R (Δ₁.tensor Δ₂) Δ₃).hom := by
      rw [MonoidalCategory.whisker_exchange]
    _ = (λ_ _).inv ≫ (W₁ ⊗ₘ (V₂ ≫ bObj R Δ₂ ◁ h)) ≫
        (bObj R Δ₁ ◁ (bMu R Δ₂ Δ₃).hom ≫ (bMu R Δ₁ (Δ₂.tensor Δ₃)).hom ≫
          bMap (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).symm.toHom) := by
      rw [bMu_assoc_symm]
      monoidal
    _ = _ := by monoidal

/-- Symmetry of `wire`. -/
theorem wire_comm' {Δ₁ Γ Δ₂ : PortBoundary} (W₁ : (qOpenTheory R).Obj (Δ₁.tensor Γ))
    (W₂ : (qOpenTheory R).Obj (Γ.swap.tensor Δ₂)) :
    (qOpenTheory R).wire W₁ W₂ =
      (qOpenTheory R).map (PortBoundary.Equiv.tensorComm Δ₂ Δ₁).toHom
        ((qOpenTheory R).wire
          ((qOpenTheory R).map (PortBoundary.Equiv.tensorComm Γ.swap Δ₂).toHom W₂)
          ((qOpenTheory R).map (PortBoundary.Equiv.tensorComm Δ₁ Γ).toHom W₁)) := by
  obtain ⟨V₁, rfl⟩ := exists_bMu W₁
  obtain ⟨V₂, rfl⟩ := exists_bMu W₂
  dsimp only
  simp only [wireHom, Category.assoc, bMu_comm, Iso.hom_inv_id, Category.comp_id]
  obtain ⟨h, rfl⟩ : ∃ h, V₂ = nameEquiv (bObj R Γ) (bObj R Δ₂) h :=
    ⟨(nameEquiv (bObj R Γ) (bObj R Δ₂)).symm V₂,
      ((nameEquiv (bObj R Γ) (bObj R Δ₂)).apply_symm_apply V₂).symm⟩
  obtain ⟨k, rfl⟩ : ∃ k, V₁ =
      nameEquiv (bObj R Γ.swap) (bObj R Δ₁) k ≫ (β_ (bObj R Γ) (bObj R Δ₁)).hom :=
    ⟨(nameEquiv _ _).symm (V₁ ≫ (β_ _ _).hom), by simp⟩
  simp only [Category.assoc, SymmetricCategory.symmetry_assoc, Equiv.symm_apply_apply]
  erw [Iso.hom_inv_id, Category.comp_id, Equiv.symm_apply_apply]
  rw [nameEquiv_apply, nameEquiv_apply, ← cup_bObj_swap Γ]
  simp only [Category.assoc]
  congr 1
  change bObj R Γ ◁ k ≫ (β_ (bObj R Γ) (bObj R Δ₁)).hom ≫ bObj R Δ₁ ◁ h ≫
      (bMu R Δ₁ Δ₂).hom =
    (β_ (bObj R Γ) (bObj R Γ.swap)).hom ≫ bObj R Γ.swap ◁ h ≫
      (β_ (bObj R Γ.swap) (bObj R Δ₂)).hom ≫ bObj R Δ₂ ◁ k ≫
        (β_ (bObj R Δ₂) (bObj R Δ₁)).hom ≫ (bMu R Δ₁ Δ₂).hom
  simp only [BraidedCategory.braiding_naturality_right_assoc, SymmetricCategory.symmetry_assoc,
    ← MonoidalCategory.whisker_exchange_assoc]

/-- The open theory satisfies the binary wiring laws with equality. -/
noncomputable instance qOpenTheory_isTraced : OpenTheory.IsTraced (qOpenTheory R) where
  toIsMonoidal := inferInstance
  wire_assoc := wire_assoc'
  wire_par_superpose := wire_par_superpose'
  wire_comm := wire_comm'

/-- Left zig-zag law: wiring the identity wire on the left. -/
theorem wire_idWire' (Γ : PortBoundary) {Δ₂ : PortBoundary}
    (W₂ : (qOpenTheory R).Obj (Γ.swap.tensor Δ₂)) :
    (qOpenTheory R).wire (OpenTheory.HasIdWire.idWire (T := qOpenTheory R) Γ) W₂ = W₂ := by
  obtain ⟨V₂, rfl⟩ := exists_bMu W₂
  change wireHom ((nameEquiv (bObj R Γ) (bObj R Γ) (𝟙 _) ≫ (bMu R Γ.swap Γ).hom) ≫
    (bMu R Γ.swap Γ).inv) _ ≫ _ = _
  simp only [wireHom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, nameEquiv_comp_bObj, Category.id_comp, Equiv.apply_symm_apply]

/-- Right zig-zag law: wiring the identity wire on the right. -/
theorem wire_idWire_right' (Γ : PortBoundary) {Δ₁ : PortBoundary}
    (W₁ : (qOpenTheory R).Obj (Δ₁.tensor Γ)) :
    (qOpenTheory R).wire W₁ (OpenTheory.HasIdWire.idWire (T := qOpenTheory R) Γ) = W₁ := by
  obtain ⟨V₁, rfl⟩ := exists_bMu W₁
  change wireHom ((V₁ ≫ (bMu R Δ₁ Γ).hom) ≫ (bMu R Δ₁ Γ).inv)
    ((nameEquiv (bObj R Γ) (bObj R Γ) (𝟙 _) ≫ (bMu R Γ.swap Γ).hom) ≫
      (bMu R Γ.swap Γ).inv) ≫ (bMu R Δ₁ Γ).hom = V₁ ≫ (bMu R Δ₁ Γ).hom
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [wireHom, Equiv.symm_apply_apply, MonoidalCategory.whiskerLeft_id, Category.comp_id]

/-- The open theory satisfies the zig-zag laws with equality. -/
noncomputable instance qOpenTheory_isCompactClosed :
    OpenTheory.IsCompactClosed (qOpenTheory R) where
  toIsTraced := inferInstance
  toHasIdWire := inferInstance
  wire_idWire := wire_idWire'
  wire_idWire_right := wire_idWire_right'
  unit_eq := closed_eq _ _

/-- **Plug-wire factorization.** The Int construction on quantum reactive systems is a PolyFun
open theory with `HasPlugWireFactor`, every law holding with equality. -/
noncomputable instance qOpenTheory_hasPlugWireFactor :
    OpenTheory.HasPlugWireFactor (qOpenTheory R) where
  toIsCompactClosed := inferInstance
  plug_eq_wire _ _ := closed_eq _ _
  plug_par_left _ _ _ := closed_eq _ _
  plug_wire_left _ _ _ := closed_eq _ _

/-! ## Observation of closed systems -/

/-- A closed system of the open theory is the class of a quantum system without events, and
equality of two such classes, the relation of PolyFun's `Observation.eq`, is step equivalence of
the systems. -/
theorem closed_mk_eq_iff
    (A B : QRSys.Obj R ((𝟙_ (IntConstruction (QSysCat R))).pos ⊗
        (bObj R PortBoundary.empty).neg).P
      ((bObj R PortBoundary.empty).pos ⊗ (𝟙_ (IntConstruction (QSysCat R))).neg).P) :
    (⟨⟦A⟧⟩ : OpenTheory.Closed (qOpenTheory R)) = ⟨⟦B⟧⟩ ↔ QRSys.StepEq A B := by
  constructor
  · intro h
    exact Quotient.exact (congrArg IntConstruction.Hom.hom h)
  · intro h
    exact IntConstruction.hom_ext (Quotient.sound h)

/-! ## The first activation of a bundled quantum system -/

/-- The first activation of the bundled quantum system `A` on the event `e`: the subinstrument
on the register with the output as outcome. -/
noncomputable def firstOut {E O : Type} (A : QRSys.Obj R E O) (e : E) : SubInstrument R R O :=
  (A.sys.step A.sys.init e).bind fun q => SubInstrument.pure q.2

/-- Step-equivalent quantum systems have the same first activation. -/
theorem firstOut_stepEq {E O : Type} {A B : QRSys.Obj R E O} (h : QRSys.StepEq A B) (e : E) :
    firstOut A e = firstOut B e := by
  induction h with
  | rel A B h =>
    obtain ⟨f, h⟩ := h
    simp only [firstOut]
    rw [← h.init_map, ← h.step _ e]
    simp [SubInstrument.bind_assoc]
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ## The bit boundary and the observation -/

open CatCrypt.Crypto.UCLoopbackObservation (bitBoundary startPkt)

/-- The bit of an output of a system on the bit boundary. -/
def bitOf : ((bObj R bitBoundary).pos ⊗ (𝟙_ (IntConstruction (QSysCat R))).neg).P → Bool :=
  Sum.elim (fun p => p.2) (fun e => Empty.elim e)

/-- The observation of a quantum open system on the bit boundary: the subinstrument on the
register of the first activation of a representative on the start packet, with the returned
bit as outcome. -/
noncomputable def obsBit (W : (qOpenTheory R).Obj bitBoundary) : SubInstrument R R Bool :=
  Quotient.lift
    (fun A => (firstOut A (Sum.inr startPkt)).bind fun o => SubInstrument.pure (bitOf o))
    (fun _ _ h => by rw [firstOut_stepEq h]) W.hom

/-! ## Tests -/

/-- The morphism `bObj R Δ ⟶ bObj R bitBoundary` named by the test `K`. -/
noncomputable def testHom {Δ : PortBoundary}
    (K : (qOpenTheory R).Obj (Δ.swap.tensor bitBoundary)) :
    bObj R Δ ⟶ bObj R bitBoundary :=
  (nameEquiv (bObj R Δ) (bObj R bitBoundary)).symm (K ≫ (bMu R Δ.swap bitBoundary).inv)

/-- The run of the quantum open system `W` against the test `K`: `W`, seen on `empty ⊗ Δ`,
wired with `K` along `Δ`, on the bit boundary. -/
noncomputable def runTest {Δ : PortBoundary} (W : (qOpenTheory R).Obj Δ)
    (K : (qOpenTheory R).Obj (Δ.swap.tensor bitBoundary)) : (qOpenTheory R).Obj bitBoundary :=
  (qOpenTheory R).map (PortBoundary.Equiv.tensorEmptyLeft bitBoundary).toHom
    ((qOpenTheory R).wire
      ((qOpenTheory R).par (OpenTheory.HasUnit.unit (T := qOpenTheory R)) W) K)

/-- The run against a test is composition with the morphism the test names. -/
theorem runTest_eq {Δ : PortBoundary} (W : (qOpenTheory R).Obj Δ)
    (K : (qOpenTheory R).Obj (Δ.swap.tensor bitBoundary)) :
    runTest W K = W ≫ testHom K := by
  change (wireHom (((λ_ _).inv ≫ ((bUnit R).hom ⊗ₘ W) ≫ (bMu R _ _).hom) ≫ (bMu R _ _).inv)
    (K ≫ (bMu R _ _).inv) ≫ (bMu R _ _).hom) ≫ bMap _ = _
  simp only [wireHom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [MonoidalCategory.tensorHom_def', Category.assoc, ← whisker_exchange_assoc,
    bMu_leftUnit, ← MonoidalCategory.whiskerLeft_comp_assoc, leftUnitor_naturality,
    Iso.inv_hom_id_assoc]
  rfl

/-! ## Quantum emulation against every test -/

/-- The quantum open system `real` emulates `ideal` when every test observes the same
subinstrument on the register with the same bit outcomes. -/
def EmulatesΩ {Δ : PortBoundary} (real ideal : (qOpenTheory R).Obj Δ) : Prop :=
  ∀ K : (qOpenTheory R).Obj (Δ.swap.tensor bitBoundary),
    obsBit (runTest real K) = obsBit (runTest ideal K)

/-- Emulation is equality of the observations after every morphism into `bObj R bitBoundary`. -/
theorem emulatesΩ_iff {Δ : PortBoundary} {real ideal : (qOpenTheory R).Obj Δ} :
    EmulatesΩ real ideal ↔
      ∀ h : bObj R Δ ⟶ bObj R bitBoundary, obsBit (real ≫ h) = obsBit (ideal ≫ h) := by
  constructor
  · intro H h
    have hK : testHom (nameEquiv (bObj R Δ) (bObj R bitBoundary) h ≫
        (bMu R Δ.swap bitBoundary).hom) = h := by
      simp [testHom]
    have := H (nameEquiv (bObj R Δ) (bObj R bitBoundary) h ≫ (bMu R Δ.swap bitBoundary).hom)
    rwa [runTest_eq, runTest_eq, hK] at this
  · intro H K
    rw [runTest_eq, runTest_eq]
    exact H _

namespace EmulatesΩ

variable {Δ : PortBoundary}

/-- Every quantum open system emulates itself. -/
theorem refl (W : (qOpenTheory R).Obj Δ) : EmulatesΩ W W :=
  fun _ => rfl

/-- Emulation is symmetric. -/
theorem symm {W₁ W₂ : (qOpenTheory R).Obj Δ} (h : EmulatesΩ W₁ W₂) : EmulatesΩ W₂ W₁ :=
  fun K => (h K).symm

/-- Emulation is transitive. -/
theorem trans {W₁ W₂ W₃ : (qOpenTheory R).Obj Δ} (h₁₂ : EmulatesΩ W₁ W₂)
    (h₂₃ : EmulatesΩ W₂ W₃) : EmulatesΩ W₁ W₃ :=
  fun K => (h₁₂ K).trans (h₂₃ K)

/-- **Sequential composition.** Emulation is preserved by composition with a morphism of the
Int construction. -/
theorem comp {Δ' : PortBoundary} {real ideal : (qOpenTheory R).Obj Δ}
    (h : EmulatesΩ real ideal) (g : bObj R Δ ⟶ bObj R Δ') :
    EmulatesΩ (real ≫ g) (ideal ≫ g) := by
  rw [emulatesΩ_iff] at h ⊢
  intro k
  simpa only [Category.assoc] using h (g ≫ k)

/-- Emulation is invariant under `map`. -/
theorem map {Δ' : PortBoundary} (f : PortBoundary.Hom Δ Δ')
    {real ideal : (qOpenTheory R).Obj Δ} (h : EmulatesΩ real ideal) :
    EmulatesΩ ((qOpenTheory R).map f real) ((qOpenTheory R).map f ideal) :=
  h.comp (bMap f)

/-- Wiring a context `C` on the right preserves emulation. -/
theorem wire_left {Δ₁ Γ Δ₂ : PortBoundary} {real ideal : (qOpenTheory R).Obj (Δ₁.tensor Γ)}
    (h : EmulatesΩ real ideal) (C : (qOpenTheory R).Obj (Γ.swap.tensor Δ₂)) :
    EmulatesΩ ((qOpenTheory R).wire real C) ((qOpenTheory R).wire ideal C) := by
  have hw : ∀ W : (qOpenTheory R).Obj (Δ₁.tensor Γ), (qOpenTheory R).wire W C =
      W ≫ ((bMu R Δ₁ Γ).inv ≫ bObj R Δ₁ ◁ (nameEquiv (bObj R Γ) (bObj R Δ₂)).symm
        (C ≫ (bMu R Γ.swap Δ₂).inv) ≫ (bMu R Δ₁ Δ₂).hom) := fun W => by
    simp only [wireHom, Category.assoc]
  rw [hw, hw]
  exact h.comp _

/-- Wiring a context `C` on the left preserves emulation. -/
theorem wire_right {Δ₁ Γ Δ₂ : PortBoundary} (C : (qOpenTheory R).Obj (Δ₁.tensor Γ))
    {real ideal : (qOpenTheory R).Obj (Γ.swap.tensor Δ₂)} (h : EmulatesΩ real ideal) :
    EmulatesΩ ((qOpenTheory R).wire C real) ((qOpenTheory R).wire C ideal) := by
  rw [wire_comm' C real, wire_comm' C ideal]
  exact ((h.map _).wire_left _).map _

/-- Putting a context `C` in parallel on the right preserves emulation. -/
theorem par_left {Δ₁ Δ₂ : PortBoundary} {real ideal : (qOpenTheory R).Obj Δ₁}
    (h : EmulatesΩ real ideal) (C : (qOpenTheory R).Obj Δ₂) :
    EmulatesΩ ((qOpenTheory R).par real C) ((qOpenTheory R).par ideal C) := by
  have hp : ∀ W : (qOpenTheory R).Obj Δ₁, (qOpenTheory R).par W C =
      W ≫ ((ρ_ (bObj R Δ₁)).inv ≫ bObj R Δ₁ ◁ C ≫ (bMu R Δ₁ Δ₂).hom) := fun W => by
    change (λ_ _).inv ≫ (W ⊗ₘ C) ≫ (bMu R Δ₁ Δ₂).hom = _
    rw [MonoidalCategory.tensorHom_def, unitors_inv_equal, Category.assoc,
      ← rightUnitor_inv_naturality_assoc]
  rw [hp, hp]
  exact h.comp _

/-- Putting a context `C` in parallel on the left preserves emulation. -/
theorem par_right {Δ₁ Δ₂ : PortBoundary} (C : (qOpenTheory R).Obj Δ₁)
    {real ideal : (qOpenTheory R).Obj Δ₂} (h : EmulatesΩ real ideal) :
    EmulatesΩ ((qOpenTheory R).par C real) ((qOpenTheory R).par C ideal) := by
  rw [← par_comm' real C, ← par_comm' ideal C]
  exact (h.par_left C).map _

/-- **Composition theorem for `wire`.** If each factor emulates its ideal, the wiring of the
factors emulates the wiring of the ideals. -/
theorem wire_compose {Δ₁ Γ Δ₂ : PortBoundary}
    {real₁ ideal₁ : (qOpenTheory R).Obj (Δ₁.tensor Γ)}
    {real₂ ideal₂ : (qOpenTheory R).Obj (Γ.swap.tensor Δ₂)} (h₁ : EmulatesΩ real₁ ideal₁)
    (h₂ : EmulatesΩ real₂ ideal₂) :
    EmulatesΩ ((qOpenTheory R).wire real₁ real₂) ((qOpenTheory R).wire ideal₁ ideal₂) :=
  (h₁.wire_left real₂).trans (wire_right ideal₁ h₂)

/-- **Composition theorem for `par`.** If each component emulates its ideal, the parallel
composition of the components emulates that of the ideals. -/
theorem par_compose {Δ₁ Δ₂ : PortBoundary} {real₁ ideal₁ : (qOpenTheory R).Obj Δ₁}
    {real₂ ideal₂ : (qOpenTheory R).Obj Δ₂} (h₁ : EmulatesΩ real₁ ideal₁)
    (h₂ : EmulatesΩ real₂ ideal₂) :
    EmulatesΩ ((qOpenTheory R).par real₁ real₂) ((qOpenTheory R).par ideal₁ ideal₂) :=
  (h₁.par_left real₂).trans (par_right ideal₁ h₂)

end EmulatesΩ

end QOpenTheory

end CatCrypt.Quantum.ReactiveUC
