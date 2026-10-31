/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCLoopbackInt
public import CatCryptCore.Crypto.UCOpenTheory
-- import all: unfolds the boundary equivalences `tensorComm` and `tensorAssoc`
import all PolyFun.Interaction.Interface

/-!
# The Int construction on systems as a PolyFun open theory

The compact closed category `IntConstruction SysCat` carries a PolyFun `OpenTheory` that
satisfies `OpenTheory.HasPlugWireFactor` with equality of objects. A port boundary `Δ` is the
object `bObj Δ = (Δ.Out, Δ.In)` of packets, and an open system on `Δ` is a morphism
`𝟙 ⟶ bObj Δ`: the class, modulo step equivalence, of a system that receives the packets of
`Δ.In` and emits the packets of `Δ.Out`. The object of `PortBoundary.swap Δ` is the dual of
`bObj Δ`, and the object of a tensor boundary is the tensor product up to the isomorphism
`bMu` of packets of a sum interface with sums of packets.

* `map f` composes with the morphism `bMap f` of the boundary morphism `f`.
* `par` is the tensor product.
* `wire` composes through names: the left system `𝟙 ⟶ A ⊗ G` is composed with the morphism
  `G ⟶ B` named by the right system `𝟙 ⟶ dualObj G ⊗ B` (`nameEquiv`).
* `plug` is the evaluation `cap` of the pairing of `bObj Δ` with its dual.
* `idWire Γ` is the name of the identity of `bObj Γ`, the unit is the isomorphism
  `𝟙 ≅ bObj empty`.

Every composite of wirings, morphisms whose underlying system is stateless, is computed by
`SysCat.trace_homOfFun`: the trace of the system of a port function whose feedback ends within
bounded fuel is the system of the resulting function.

A closed system is the class of a system without events, and equality of closed systems, the
relation of PolyFun's `Observation.eq`, is step equivalence of representatives
(`closed_mk_eq_iff`). Systems without events are all step equivalent, so `𝟙 ⟶ bObj empty` has
one element (`closed_eq`) and every law whose two sides are closed systems holds by `closed_eq`.

## Main definitions

* `SysCat.fbIter`: the feedback of a port function, run with bounded fuel.
* `IntSys.dualObj`: the dual `(X⁻, X⁺)` of an object `X`.
* `IntSys.cup`, `IntSys.cap`: the pairing of `dualObj X` with `X` by forwarding systems.
* `IntSys.nameEquiv`: morphisms `G ⟶ B` and their names `𝟙 ⟶ dualObj G ⊗ B`.
* `UCLoopbackOpenTheory.loopOpenTheory`: the open theory.

## Main results

* `SysCat.trace_homOfFun`: the trace of a stateless system with bounded feedback.
* `IntSys.cup_cap_zigzag`, `IntSys.cap_cup_zigzag`: the zig-zag laws of `cup` and `cap`.
* `UCLoopbackOpenTheory.loopOpenTheory_hasPlugWireFactor`: the open theory satisfies
  `HasPlugWireFactor`.
* `UCLoopbackOpenTheory.closed_mk_eq_iff`: equality of closed systems is step equivalence.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CategoryTheory MonoidalCategory BraidedCategory

namespace SysCat

/-- The feedback of the port function `f` from `x` with `n` further passes along the wire: the
output it reaches, or `none` when the fuel runs out. -/
def fbIter {Q R U : Type} (f : Q ⊕ U → R ⊕ U) : ℕ → Q ⊕ U → Option R
  | 0, x => Sum.elim some (fun _ => none) (f x)
  | n + 1, x => Sum.elim some (fun u => fbIter f n (.inr u)) (f x)

/-- The unbounded activation of the stateless system of `f` reaches the output of `fbIter`. -/
theorem fbRunω_ofFun {Q R U : Type} (f : Q ⊕ U → R ⊕ U) :
    ∀ (n : ℕ) (x : Q ⊕ U) (r : R), fbIter f n x = some r →
      (Sys.ofFun f).fbRunω x () = SPComp.pure ((), r) := by
  intro n
  induction n with
  | zero =>
    intro x r h
    rw [Sys.fbRunω_eq, Sys.ofFun_step, SPComp.pure_bind]
    rcases hx : f x with o | u <;> simp_all [fbIter]
  | succ n ih =>
    intro x r h
    rw [Sys.fbRunω_eq, Sys.ofFun_step, SPComp.pure_bind]
    rcases hx : f x with o | u
    · simp_all [fbIter]
    · simp only [fbIter, hx, Sum.elim_inr] at h
      exact ih _ _ h

/-- **Trace of a stateless system.** When the feedback of the port function `f` ends from every
outer event, the trace of its system is the system of the function it computes. -/
theorem trace_homOfFun {X Y U : SysCat} (f : X.P ⊕ U.P → Y.P ⊕ U.P) (g : X.P → Y.P)
    (h : ∀ x, ∃ n, fbIter f n (.inl x) = some (g x)) :
    TracedCategory.trace U (homOfFun (X := X ⊗ U) (Y := Y ⊗ U) f) = homOfFun g := by
  refine Quotient.sound (Sys.StepMapOn.of_step (R := (Sys.ofFun f).loopbackω)
    (I := Sys.ofFun g) id rfl fun t e => ?_).stepEq
  obtain ⟨n, hn⟩ := h e
  change SPComp.map _ ((Sys.ofFun f).fbRunω (.inl e) t) = SPComp.pure (t, g e)
  rw [fbRunω_ofFun f n _ _ hn]
  simp [SPComp.map]

/-- Morphisms out of a port type without ports are equal: their systems have no events. -/
theorem hom_eq_of_isEmpty {X Y : SysCat} (hX : IsEmpty X.P) (a b : X ⟶ Y) : a = b := by
  induction a using Quotient.inductionOn with
  | h A =>
    induction b using Quotient.inductionOn with
    | h B =>
      exact Quotient.sound (Sys.StepMapOn.of_step (R := A.sys) (I := B.sys)
        (fun _ => B.sys.init) rfl fun _ e => isEmptyElim e).stepEq

/-- Unfolding lemma of the symmetry. -/
theorem braiding_def (X Y : SysCat) :
    β_ X Y = isoOfEquiv (X := X ⊗ Y) (Y := Y ⊗ X) (Equiv.sumComm X.P Y.P) :=
  rfl

/-- The tensor product of morphisms given by functions, in the monoidal notation. -/
theorem homOfFun_tensorHom' {X₁ Y₁ X₂ Y₂ : SysCat} (f : X₁.P → Y₁.P) (g : X₂.P → Y₂.P) :
    homOfFun f ⊗ₘ homOfFun g = homOfFun (X := X₁ ⊗ X₂) (Y := Y₁ ⊗ Y₂) (Sum.map f g) :=
  homOfFun_tensorHom f g

end SysCat

/-! ## Forwarding pairings in the Int construction -/

namespace IntSys

open SysCat IntConstruction

/-- The dual `(X⁻, X⁺)` of `X`, the object `IntConstruction.dual X` unfolded. -/
abbrev dualObj (X : IntConstruction SysCat) : IntConstruction SysCat :=
  ⟨X.neg, X.pos⟩

/-- The forwarding system `𝟙 ⟶ dualObj X ⊗ X`: a packet received on one side is emitted on the
other. -/
noncomputable def cup (X : IntConstruction SysCat) :
    𝟙_ (IntConstruction SysCat) ⟶ dualObj X ⊗ X :=
  ⟨homOfFun fun x => match x with
      | .inr (.inl p) => .inl (.inr p)
      | .inr (.inr n) => .inl (.inl n)⟩

/-- The forwarding system `X ⊗ dualObj X ⟶ 𝟙`: a packet emitted on one side is received on the
other. -/
noncomputable def cap (X : IntConstruction SysCat) :
    X ⊗ dualObj X ⟶ 𝟙_ (IntConstruction SysCat) :=
  ⟨homOfFun fun x => match x with
      | .inl (.inl p) => .inr (.inr p)
      | .inl (.inr n) => .inr (.inl n)⟩

/-- First zig-zag law of `cup` and `cap`. -/
theorem cup_cap_zigzag (X : IntConstruction SysCat) :
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
theorem cap_cup_zigzag (X : IntConstruction SysCat) :
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
noncomputable def cupCapPairing (X : IntConstruction SysCat) : ExactPairing (dualObj X) X where
  coevaluation' := cup X
  evaluation' := cap X
  coevaluation_evaluation' := cup_cap_zigzag X
  evaluation_coevaluation' := cap_cup_zigzag X

/-- Unfolding lemma of the symmetry of the Int construction. -/
theorem braiding_hom (X Y : IntConstruction SysCat) :
    (β_ X Y).hom = IntConstruction.mkHom (β_ X.pos Y.pos).hom (β_ X.neg Y.neg).inv :=
  rfl

/-- The forwarding system of the dual, followed by the symmetry, is the forwarding system. -/
theorem cup_dual_braiding (X : IntConstruction SysCat) :
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
noncomputable def nameEquiv (G B : IntConstruction SysCat) :
    (G ⟶ B) ≃ (𝟙_ (IntConstruction SysCat) ⟶ dualObj G ⊗ B) :=
  ((ρ_ G).homCongr (Iso.refl B)).symm.trans
    (@tensorLeftHomEquiv _ _ _ (𝟙_ _) (dualObj G) G B (cupCapPairing G))

/-- The name of `h` is the forwarding system followed by `h`. -/
theorem nameEquiv_apply {G B : IntConstruction SysCat} (h : G ⟶ B) :
    nameEquiv G B h = cup G ≫ dualObj G ◁ h := by
  dsimp only [nameEquiv, tensorLeftHomEquiv, Iso.homCongr, Equiv.trans_apply,
    Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
  monoidal

/-- Naming commutes with composition on the right. -/
theorem nameEquiv_comp {G B B' : IntConstruction SysCat} (h : G ⟶ B) (k : B ⟶ B') :
    nameEquiv G B' (h ≫ k) = nameEquiv G B h ≫ dualObj G ◁ k := by
  simp only [nameEquiv_apply, MonoidalCategory.whiskerLeft_comp, Category.assoc]

/-- Reading a name commutes with composition on the right. -/
theorem nameEquiv_symm_comp {G B B' : IntConstruction SysCat}
    (V : 𝟙_ (IntConstruction SysCat) ⟶ dualObj G ⊗ B) (k : B ⟶ B') :
    (nameEquiv G B').symm (V ≫ dualObj G ◁ k) = (nameEquiv G B).symm V ≫ k := by
  rw [Equiv.symm_apply_eq, nameEquiv_comp, Equiv.apply_symm_apply]

/-- Reading a name commutes with composition on the right, with a composite name. -/
theorem nameEquiv_symm_comp_assoc {G B B' : IntConstruction SysCat} {Z : IntConstruction SysCat}
    (V : 𝟙_ (IntConstruction SysCat) ⟶ Z) (V' : Z ⟶ dualObj G ⊗ B) (k : B ⟶ B') :
    (nameEquiv G B').symm (V ≫ V' ≫ dualObj G ◁ k) = (nameEquiv G B).symm (V ≫ V') ≫ k := by
  rw [← Category.assoc, nameEquiv_symm_comp]

/-- The tensor product of two morphisms of the form `mkHom`, in the monoidal notation. -/
theorem mkHom_tensorHom_mkHom {X₁ Y₁ X₂ Y₂ : IntConstruction SysCat} (u : X₁.pos ⟶ Y₁.pos)
    (v : Y₁.neg ⟶ X₁.neg) (u' : X₂.pos ⟶ Y₂.pos) (v' : Y₂.neg ⟶ X₂.neg) :
    IntConstruction.mkHom u v ⊗ₘ IntConstruction.mkHom u' v' =
      IntConstruction.mkHom (X := X₁ ⊗ X₂) (Y := Y₁ ⊗ Y₂) (u ⊗ₘ u') (v ⊗ₘ v') :=
  IntConstruction.tensorHom_mkHom u v u' v'

end IntSys

end CatCrypt.Crypto.UCTransparent

namespace CatCrypt.Crypto.UCLoopbackOpenTheory

open CatCrypt.Core CategoryTheory MonoidalCategory BraidedCategory
open CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.SysCat
open CatCrypt.Crypto.UCTransparent.IntSys CatCrypt.Crypto.UCOpenTheory
open Interaction Interaction.Open

/-! ## Port boundaries as objects of the Int construction -/

/-- Sums of packets are the packets of the sum interface. -/
def packetSumEquiv (I J : Interface.{0, 0}) :
    Interface.Packet I ⊕ Interface.Packet J ≃ Interface.Packet (Interface.sum I J) :=
  ⟨insum, unsum, unsum_insum, insum_unsum⟩

/-- The empty boundary has no input packets. -/
instance isEmpty_packet_empty_in : IsEmpty (Interface.Packet PortBoundary.empty.In) :=
  ⟨fun p => noEv p⟩

/-- The empty boundary has no output packets. -/
instance isEmpty_packet_empty_out : IsEmpty (Interface.Packet PortBoundary.empty.Out) :=
  ⟨fun p => noEv p⟩

/-- The object of the port boundary `Δ`: positive component the packets of `Δ.Out`, negative
component the packets of `Δ.In`. -/
abbrev bObj (Δ : PortBoundary) : IntConstruction SysCat :=
  ⟨⟨Interface.Packet Δ.Out⟩, ⟨Interface.Packet Δ.In⟩⟩

/-- The morphism of a boundary morphism: outputs translated forward, inputs backward. -/
noncomputable def bMap {Δ₁ Δ₂ : PortBoundary} (f : PortBoundary.Hom Δ₁ Δ₂) :
    bObj Δ₁ ⟶ bObj Δ₂ :=
  IntConstruction.mkHom (homOfFun (Interface.Hom.mapPacket f.onOut))
    (homOfFun (Interface.Hom.mapPacket f.onIn))

/-- The object of a tensor boundary is the tensor product of the objects. -/
noncomputable def bMu (Δ₁ Δ₂ : PortBoundary) : bObj Δ₁ ⊗ bObj Δ₂ ≅ bObj (Δ₁.tensor Δ₂) :=
  IntConstruction.mkIso (isoOfEquiv (packetSumEquiv _ _)) (isoOfEquiv (packetSumEquiv _ _))

/-- The object of the empty boundary is the unit. -/
noncomputable def bUnit : 𝟙_ (IntConstruction SysCat) ≅ bObj PortBoundary.empty :=
  IntConstruction.mkIso (isoOfEquiv (Equiv.equivEmpty _).symm)
    (isoOfEquiv (Equiv.equivEmpty _).symm)

/-- The morphism of the identity boundary morphism is the identity. -/
theorem bMap_id (Δ : PortBoundary) : bMap (PortBoundary.Hom.id Δ) = 𝟙 (bObj Δ) := by
  simp only [bMap, PortBoundary.Hom.id, Interface.Hom.mapPacket_id, IntConstruction.id_eq_mkHom]
  rfl

/-- The morphism of a composite boundary morphism is the composite. -/
theorem bMap_comp {Δ₁ Δ₂ Δ₃ : PortBoundary} (g : PortBoundary.Hom Δ₂ Δ₃)
    (f : PortBoundary.Hom Δ₁ Δ₂) : bMap (PortBoundary.Hom.comp g f) = bMap f ≫ bMap g := by
  simp only [bMap, PortBoundary.Hom.comp, IntConstruction.mkHom_comp_mkHom, homOfFun_comp,
    Interface.Hom.mapPacket_comp]

/-- `bMu` is natural in the two boundaries. -/
theorem bMu_bMap {Δ₁ Δ₂ Δ₁' Δ₂' : PortBoundary} (f₁ : PortBoundary.Hom Δ₁ Δ₁')
    (f₂ : PortBoundary.Hom Δ₂ Δ₂') :
    (bMu Δ₁ Δ₂).hom ≫ bMap (f₁.tensor f₂) = (bMap f₁ ⊗ₘ bMap f₂) ≫ (bMu Δ₁' Δ₂').hom := by
  simp only [bMu, bMap, IntConstruction.mkIso_hom, mkHom_tensorHom_mkHom,
    IntConstruction.mkHom_comp_mkHom, isoOfEquiv_hom, isoOfEquiv_inv, homOfFun_tensorHom',
    homOfFun_comp, PortBoundary.Hom.tensor]
  congr 2 <;> funext x
  · exact mapPacket_sum_insum _ _ x
  · exact (unsum_mapPacket_sum _ _ x)

/-- `bMu` and the associativity of boundaries. -/
theorem bMu_assoc (Δ₁ Δ₂ Δ₃ : PortBoundary) :
    (bMu Δ₁ Δ₂).hom ▷ bObj Δ₃ ≫ (bMu (Δ₁.tensor Δ₂) Δ₃).hom ≫
        bMap (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).toHom =
      (α_ _ _ _).hom ≫ bObj Δ₁ ◁ (bMu Δ₂ Δ₃).hom ≫ (bMu Δ₁ (Δ₂.tensor Δ₃)).hom := by
  simp only [bMu, bMap, IntConstruction.mkIso_hom, IntConstruction.mkHom_whiskerRight,
    IntConstruction.whiskerLeft_mkHom, IntConstruction.associator_hom,
    IntConstruction.mkHom_comp_mkHom, isoOfEquiv_hom, isoOfEquiv_inv, associator_def,
    whiskerLeft_homOfFun, whiskerRight_homOfFun, homOfFun_comp]
  congr 2 <;> funext x
  · rcases x with ((⟨a, b⟩ | ⟨a, b⟩) | ⟨a, b⟩) <;> rfl
  · rcases x with ⟨a | a | a, b⟩ <;> rfl

/-- `bMu` and the inverse associativity of boundaries. -/
theorem bMu_assoc_symm (Δ₁ Δ₂ Δ₃ : PortBoundary) :
    bObj Δ₁ ◁ (bMu Δ₂ Δ₃).hom ≫ (bMu Δ₁ (Δ₂.tensor Δ₃)).hom ≫
        bMap (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).symm.toHom =
      (α_ _ _ _).inv ≫ (bMu Δ₁ Δ₂).hom ▷ bObj Δ₃ ≫ (bMu (Δ₁.tensor Δ₂) Δ₃).hom := by
  simp only [bMu, bMap, IntConstruction.mkIso_hom, IntConstruction.mkHom_whiskerRight,
    IntConstruction.whiskerLeft_mkHom, IntConstruction.associator_inv,
    IntConstruction.mkHom_comp_mkHom, isoOfEquiv_hom, isoOfEquiv_inv, associator_def,
    whiskerLeft_homOfFun, whiskerRight_homOfFun, homOfFun_comp]
  congr 2 <;> funext x
  · rcases x with (⟨a, b⟩ | (⟨a, b⟩ | ⟨a, b⟩)) <;> rfl
  · rcases x with ⟨(a | a) | a, b⟩ <;> rfl

/-- `bMu` and the symmetry of boundaries. -/
theorem bMu_comm (Δ₁ Δ₂ : PortBoundary) :
    (bMu Δ₁ Δ₂).hom ≫ bMap (PortBoundary.Equiv.tensorComm Δ₁ Δ₂).toHom =
      (β_ _ _).hom ≫ (bMu Δ₂ Δ₁).hom := by
  simp only [bMu, bMap, braiding_hom, IntConstruction.mkIso_hom,
    IntConstruction.mkHom_comp_mkHom, isoOfEquiv_hom, isoOfEquiv_inv, braiding_def,
    homOfFun_comp]
  congr 2 <;> funext x
  · rcases x with ⟨a, b⟩ | ⟨a, b⟩ <;> rfl
  · rcases x with ⟨a | a, b⟩ <;> rfl

/-- `bMu` and the left unit of boundaries. -/
theorem bMu_leftUnit (Δ : PortBoundary) :
    bUnit.hom ▷ bObj Δ ≫ (bMu PortBoundary.empty Δ).hom ≫
        bMap (PortBoundary.Equiv.tensorEmptyLeft Δ).toHom = (λ_ (bObj Δ)).hom := by
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
    bObj Δ ◁ bUnit.hom ≫ (bMu Δ PortBoundary.empty).hom ≫
        bMap (PortBoundary.Equiv.tensorEmptyRight Δ).toHom = (ρ_ (bObj Δ)).hom := by
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
    bMap (f₁.tensor f₂) ≫ (bMu Δ₁' Δ₂').inv = (bMu Δ₁ Δ₂).inv ≫ (bMap f₁ ⊗ₘ bMap f₂) := by
  rw [Iso.comp_inv_eq, Category.assoc, ← bMu_bMap, Iso.inv_hom_id_assoc]

/-- `nameEquiv_symm_comp_assoc` at the object of a boundary, whose dual is the object of the
swapped boundary. -/
theorem nameEquiv_symm_bObj {Γ : PortBoundary} {B B' Z : IntConstruction SysCat}
    (V : 𝟙_ (IntConstruction SysCat) ⟶ Z) (V' : Z ⟶ bObj Γ.swap ⊗ B) (k : B ⟶ B') :
    (nameEquiv (bObj Γ) B').symm (V ≫ V' ≫ bObj Γ.swap ◁ k) =
      (nameEquiv (bObj Γ) B).symm (V ≫ V') ≫ k :=
  nameEquiv_symm_comp_assoc (G := bObj Γ) (B := B) (B' := B') V V' k

/-- `nameEquiv_comp` at the object of a boundary. -/
theorem nameEquiv_comp_bObj {Γ : PortBoundary} {B B' : IntConstruction SysCat}
    (h : bObj Γ ⟶ B) (k : B ⟶ B') :
    nameEquiv (bObj Γ) B h ≫ bObj Γ.swap ◁ k = nameEquiv (bObj Γ) B' (h ≫ k) :=
  (nameEquiv_comp (G := bObj Γ) h k).symm

/-- `cup_dual_braiding` at the object of a boundary. -/
theorem cup_bObj_swap (Γ : PortBoundary) :
    cup (bObj Γ.swap) ≫ (β_ (bObj Γ) (bObj Γ.swap)).hom = cup (bObj Γ) :=
  cup_dual_braiding (bObj Γ)

/-! ## The open theory -/

/-- The wiring of `V₁ : 𝟙 ⟶ A ⊗ G` with `V₂ : 𝟙 ⟶ dualObj G ⊗ B`: `V₁` followed on `G` by the
morphism `G ⟶ B` that `V₂` names. -/
noncomputable def wireHom {A G B : IntConstruction SysCat}
    (V₁ : 𝟙_ (IntConstruction SysCat) ⟶ A ⊗ G)
    (V₂ : 𝟙_ (IntConstruction SysCat) ⟶ dualObj G ⊗ B) :
    𝟙_ (IntConstruction SysCat) ⟶ A ⊗ B :=
  V₁ ≫ A ◁ (nameEquiv G B).symm V₂

/-- The Int construction on systems as a PolyFun open theory: an open system on `Δ` is a
morphism `𝟙 ⟶ bObj Δ`, `map` composes with `bMap`, `par` is the tensor product, `wire`
composes through names and `plug` is the evaluation `cap`. -/
noncomputable abbrev loopOpenTheory : OpenTheory where
  Obj Δ := 𝟙_ (IntConstruction SysCat) ⟶ bObj Δ
  map f W := W ≫ bMap f
  par {Δ₁ Δ₂} W₁ W₂ := (λ_ _).inv ≫ (W₁ ⊗ₘ W₂) ≫ (bMu Δ₁ Δ₂).hom
  wire {Δ₁ Γ Δ₂} W₁ W₂ :=
    wireHom (G := bObj Γ) (W₁ ≫ (bMu Δ₁ Γ).inv) (W₂ ≫ (bMu Γ.swap Δ₂).inv) ≫
      (bMu Δ₁ Δ₂).hom
  plug {Δ} W K := (λ_ _).inv ≫ (W ⊗ₘ K) ≫ cap (bObj Δ) ≫ bUnit.hom

/-- The unit of the open theory: the isomorphism `𝟙 ≅ bObj empty`. -/
noncomputable instance : OpenTheory.HasUnit loopOpenTheory :=
  ⟨bUnit.hom⟩

/-- The identity wire on `Γ`: the name of the identity of `bObj Γ`. -/
noncomputable instance : OpenTheory.HasIdWire loopOpenTheory :=
  ⟨fun Γ => nameEquiv (bObj Γ) (bObj Γ) (𝟙 _) ≫ (bMu Γ.swap Γ).hom⟩

/-- A closed system has no events: `𝟙 ⟶ bObj empty` has one element. -/
theorem closed_eq (a b : loopOpenTheory.Obj PortBoundary.empty) : a = b :=
  IntConstruction.hom_ext (hom_eq_of_isEmpty ⟨fun x => by
    rcases x with e | p
    · exact Empty.elim e
    · exact noEv p⟩ _ _)

/-- The open theory is lawful: `map` is functorial, `par`, `wire`, `plug` are natural. -/
instance loopOpenTheory_isLawful : OpenTheory.IsLawful loopOpenTheory where
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
theorem par_assoc' {Δ₁ Δ₂ Δ₃ : PortBoundary} (W₁ : loopOpenTheory.Obj Δ₁)
    (W₂ : loopOpenTheory.Obj Δ₂) (W₃ : loopOpenTheory.Obj Δ₃) :
    loopOpenTheory.map (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).toHom
        (loopOpenTheory.par (loopOpenTheory.par W₁ W₂) W₃) =
      loopOpenTheory.par W₁ (loopOpenTheory.par W₂ W₃) := by
  dsimp only
  calc _ = (λ_ _).inv ≫ (((λ_ _).inv ≫ (W₁ ⊗ₘ W₂)) ⊗ₘ W₃) ≫
        ((bMu Δ₁ Δ₂).hom ▷ bObj Δ₃ ≫ (bMu (Δ₁.tensor Δ₂) Δ₃).hom ≫
          bMap (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).toHom) := by monoidal
    _ = (λ_ _).inv ≫ (((λ_ _).inv ≫ (W₁ ⊗ₘ W₂)) ⊗ₘ W₃) ≫
        ((α_ _ _ _).hom ≫ bObj Δ₁ ◁ (bMu Δ₂ Δ₃).hom ≫ (bMu Δ₁ (Δ₂.tensor Δ₃)).hom) := by
      rw [bMu_assoc]
    _ = _ := by monoidal

/-- Commutativity of `par`. -/
theorem par_comm' {Δ₁ Δ₂ : PortBoundary} (W₁ : loopOpenTheory.Obj Δ₁)
    (W₂ : loopOpenTheory.Obj Δ₂) :
    loopOpenTheory.map (PortBoundary.Equiv.tensorComm Δ₁ Δ₂).toHom (loopOpenTheory.par W₁ W₂) =
      loopOpenTheory.par W₂ W₁ := by
  dsimp only
  rw [Category.assoc, Category.assoc, bMu_comm, BraidedCategory.braiding_naturality_assoc,
    braiding_tensorUnit_left, Category.assoc, Iso.inv_hom_id_assoc, ← unitors_inv_equal]

/-- Left unit law of `par`. -/
theorem par_leftUnit' {Δ : PortBoundary} (W : loopOpenTheory.Obj Δ) :
    loopOpenTheory.map (PortBoundary.Equiv.tensorEmptyLeft Δ).toHom
      (loopOpenTheory.par (OpenTheory.HasUnit.unit (T := loopOpenTheory)) W) = W := by
  change ((λ_ _).inv ≫ (bUnit.hom ⊗ₘ W) ≫ (bMu _ _).hom) ≫ bMap _ = W
  rw [MonoidalCategory.tensorHom_def', Category.assoc, Category.assoc, Category.assoc,
    bMu_leftUnit, MonoidalCategory.leftUnitor_naturality, Iso.inv_hom_id_assoc]

/-- Right unit law of `par`. -/
theorem par_rightUnit' {Δ : PortBoundary} (W : loopOpenTheory.Obj Δ) :
    loopOpenTheory.map (PortBoundary.Equiv.tensorEmptyRight Δ).toHom
      (loopOpenTheory.par W (OpenTheory.HasUnit.unit (T := loopOpenTheory))) = W := by
  change ((λ_ _).inv ≫ (W ⊗ₘ bUnit.hom) ≫ (bMu _ _).hom) ≫ bMap _ = W
  rw [MonoidalCategory.tensorHom_def, Category.assoc, Category.assoc, Category.assoc,
    bMu_rightUnit, MonoidalCategory.rightUnitor_naturality, unitors_inv_equal,
    Iso.inv_hom_id_assoc]

/-- The open theory satisfies the symmetric monoidal laws of `par` with equality. -/
noncomputable instance loopOpenTheory_isMonoidal : OpenTheory.IsMonoidal loopOpenTheory where
  toIsLawful := inferInstance
  toHasUnit := inferInstance
  par_assoc := par_assoc'
  par_comm := par_comm'
  par_leftUnit := par_leftUnit'
  par_rightUnit := par_rightUnit'

/-- Every open system on a tensor boundary is `V ≫ bMu.hom` for a morphism `V` into the
tensor product. -/
theorem exists_bMu {Δ₁ Δ₂ : PortBoundary} (W : loopOpenTheory.Obj (Δ₁.tensor Δ₂)) :
    ∃ V : 𝟙_ (IntConstruction SysCat) ⟶ bObj Δ₁ ⊗ bObj Δ₂, W = V ≫ (bMu Δ₁ Δ₂).hom :=
  ⟨W ≫ (bMu Δ₁ Δ₂).inv, by simp⟩

/-- Associativity of `wire`. -/
theorem wire_assoc' {Δ₁ Γ₁ Γ₂ Δ₃ : PortBoundary} (W₁ : loopOpenTheory.Obj (Δ₁.tensor Γ₁))
    (W₂ : loopOpenTheory.Obj (Γ₁.swap.tensor Γ₂)) (W₃ : loopOpenTheory.Obj (Γ₂.swap.tensor Δ₃)) :
    loopOpenTheory.wire (loopOpenTheory.wire W₁ W₂) W₃ =
      loopOpenTheory.wire W₁ (loopOpenTheory.wire W₂ W₃) := by
  dsimp only
  simp only [wireHom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [nameEquiv_symm_bObj, MonoidalCategory.whiskerLeft_comp, Category.assoc]

/-- Superposition of `par` and `wire`. -/
theorem wire_par_superpose' {Δ₁ Δ₂ Γ Δ₃ : PortBoundary} (W₁ : loopOpenTheory.Obj Δ₁)
    (W₂ : loopOpenTheory.Obj (Δ₂.tensor Γ)) (W₃ : loopOpenTheory.Obj (Γ.swap.tensor Δ₃)) :
    loopOpenTheory.wire
        (loopOpenTheory.map (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Γ).symm.toHom
          (loopOpenTheory.par W₁ W₂)) W₃ =
      loopOpenTheory.map (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).symm.toHom
        (loopOpenTheory.par W₁ (loopOpenTheory.wire W₂ W₃)) := by
  obtain ⟨V₂, rfl⟩ := exists_bMu W₂
  dsimp only
  simp only [wireHom, Category.assoc, Iso.hom_inv_id_assoc]
  generalize (nameEquiv (bObj Γ) (bObj Δ₃)).symm (W₃ ≫ (bMu Γ.swap Δ₃).inv) = h
  calc _ = (λ_ _).inv ≫ (W₁ ⊗ₘ V₂) ≫
        (bObj Δ₁ ◁ (bMu Δ₂ Γ).hom ≫ (bMu Δ₁ (Δ₂.tensor Γ)).hom ≫
          bMap (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Γ).symm.toHom) ≫
        (bMu (Δ₁.tensor Δ₂) Γ).inv ≫ bObj (Δ₁.tensor Δ₂) ◁ h ≫
          (bMu (Δ₁.tensor Δ₂) Δ₃).hom := by monoidal
    _ = (λ_ _).inv ≫ (W₁ ⊗ₘ V₂) ≫ (α_ _ _ _).inv ≫
        ((bMu Δ₁ Δ₂).hom ▷ bObj Γ ≫ bObj (Δ₁.tensor Δ₂) ◁ h) ≫
          (bMu (Δ₁.tensor Δ₂) Δ₃).hom := by
      rw [bMu_assoc_symm]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = (λ_ _).inv ≫ (W₁ ⊗ₘ V₂) ≫ (α_ _ _ _).inv ≫
        ((bObj Δ₁ ⊗ bObj Δ₂) ◁ h ≫ (bMu Δ₁ Δ₂).hom ▷ bObj Δ₃) ≫
          (bMu (Δ₁.tensor Δ₂) Δ₃).hom := by
      rw [MonoidalCategory.whisker_exchange]
    _ = (λ_ _).inv ≫ (W₁ ⊗ₘ (V₂ ≫ bObj Δ₂ ◁ h)) ≫
        (bObj Δ₁ ◁ (bMu Δ₂ Δ₃).hom ≫ (bMu Δ₁ (Δ₂.tensor Δ₃)).hom ≫
          bMap (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).symm.toHom) := by
      rw [bMu_assoc_symm]
      monoidal
    _ = _ := by monoidal

/-- Symmetry of `wire`. -/
theorem wire_comm' {Δ₁ Γ Δ₂ : PortBoundary} (W₁ : loopOpenTheory.Obj (Δ₁.tensor Γ))
    (W₂ : loopOpenTheory.Obj (Γ.swap.tensor Δ₂)) :
    loopOpenTheory.wire W₁ W₂ =
      loopOpenTheory.map (PortBoundary.Equiv.tensorComm Δ₂ Δ₁).toHom
        (loopOpenTheory.wire
          (loopOpenTheory.map (PortBoundary.Equiv.tensorComm Γ.swap Δ₂).toHom W₂)
          (loopOpenTheory.map (PortBoundary.Equiv.tensorComm Δ₁ Γ).toHom W₁)) := by
  obtain ⟨V₁, rfl⟩ := exists_bMu W₁
  obtain ⟨V₂, rfl⟩ := exists_bMu W₂
  dsimp only
  simp only [wireHom, Category.assoc, bMu_comm, Iso.hom_inv_id, Category.comp_id]
  obtain ⟨h, rfl⟩ : ∃ h, V₂ = nameEquiv (bObj Γ) (bObj Δ₂) h :=
    ⟨(nameEquiv (bObj Γ) (bObj Δ₂)).symm V₂,
      ((nameEquiv (bObj Γ) (bObj Δ₂)).apply_symm_apply V₂).symm⟩
  obtain ⟨k, rfl⟩ : ∃ k, V₁ =
      nameEquiv (bObj Γ.swap) (bObj Δ₁) k ≫ (β_ (bObj Γ) (bObj Δ₁)).hom :=
    ⟨(nameEquiv _ _).symm (V₁ ≫ (β_ _ _).hom), by simp⟩
  simp only [Category.assoc, SymmetricCategory.symmetry_assoc, Equiv.symm_apply_apply]
  erw [Iso.hom_inv_id, Category.comp_id, Equiv.symm_apply_apply]
  rw [nameEquiv_apply, nameEquiv_apply, ← cup_bObj_swap Γ]
  simp only [Category.assoc]
  congr 1
  change bObj Γ ◁ k ≫ (β_ (bObj Γ) (bObj Δ₁)).hom ≫ bObj Δ₁ ◁ h ≫ (bMu Δ₁ Δ₂).hom =
    (β_ (bObj Γ) (bObj Γ.swap)).hom ≫ bObj Γ.swap ◁ h ≫ (β_ (bObj Γ.swap) (bObj Δ₂)).hom ≫
      bObj Δ₂ ◁ k ≫ (β_ (bObj Δ₂) (bObj Δ₁)).hom ≫ (bMu Δ₁ Δ₂).hom
  simp only [BraidedCategory.braiding_naturality_right_assoc, SymmetricCategory.symmetry_assoc,
    ← MonoidalCategory.whisker_exchange_assoc]

/-- The open theory satisfies the binary wiring laws with equality. -/
noncomputable instance loopOpenTheory_isTraced : OpenTheory.IsTraced loopOpenTheory where
  toIsMonoidal := inferInstance
  wire_assoc := wire_assoc'
  wire_par_superpose := wire_par_superpose'
  wire_comm := wire_comm'

/-- Left zig-zag law: wiring the identity wire on the left. -/
theorem wire_idWire' (Γ : PortBoundary) {Δ₂ : PortBoundary}
    (W₂ : loopOpenTheory.Obj (Γ.swap.tensor Δ₂)) :
    loopOpenTheory.wire (OpenTheory.HasIdWire.idWire (T := loopOpenTheory) Γ) W₂ = W₂ := by
  obtain ⟨V₂, rfl⟩ := exists_bMu W₂
  change wireHom ((nameEquiv (bObj Γ) (bObj Γ) (𝟙 _) ≫ (bMu Γ.swap Γ).hom) ≫
    (bMu Γ.swap Γ).inv) _ ≫ _ = _
  simp only [wireHom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, nameEquiv_comp_bObj, Category.id_comp, Equiv.apply_symm_apply]

/-- Right zig-zag law: wiring the identity wire on the right. -/
theorem wire_idWire_right' (Γ : PortBoundary) {Δ₁ : PortBoundary}
    (W₁ : loopOpenTheory.Obj (Δ₁.tensor Γ)) :
    loopOpenTheory.wire W₁ (OpenTheory.HasIdWire.idWire (T := loopOpenTheory) Γ) = W₁ := by
  obtain ⟨V₁, rfl⟩ := exists_bMu W₁
  change wireHom ((V₁ ≫ (bMu Δ₁ Γ).hom) ≫ (bMu Δ₁ Γ).inv)
    ((nameEquiv (bObj Γ) (bObj Γ) (𝟙 _) ≫ (bMu Γ.swap Γ).hom) ≫ (bMu Γ.swap Γ).inv) ≫
      (bMu Δ₁ Γ).hom = V₁ ≫ (bMu Δ₁ Γ).hom
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [wireHom, Equiv.symm_apply_apply, MonoidalCategory.whiskerLeft_id, Category.comp_id]

/-- The open theory satisfies the zig-zag laws with equality. -/
noncomputable instance loopOpenTheory_isCompactClosed :
    OpenTheory.IsCompactClosed loopOpenTheory where
  toIsTraced := inferInstance
  toHasIdWire := inferInstance
  wire_idWire := wire_idWire'
  wire_idWire_right := wire_idWire_right'
  unit_eq := closed_eq _ _

/-- **Plug-wire factorization.** The Int construction on systems is a PolyFun open theory with
`HasPlugWireFactor`, every law holding with equality. -/
noncomputable instance loopOpenTheory_hasPlugWireFactor :
    OpenTheory.HasPlugWireFactor loopOpenTheory where
  toIsCompactClosed := inferInstance
  plug_eq_wire _ _ := closed_eq _ _
  plug_par_left _ _ _ := closed_eq _ _
  plug_wire_left _ _ _ := closed_eq _ _

/-! ## Observation of closed systems -/

/-- A closed system of the open theory is the class of a system without events, and equality of
two such classes, the relation of PolyFun's `Observation.eq`, is step equivalence of the
systems. -/
theorem closed_mk_eq_iff
    (A B : SysObj ((𝟙_ (IntConstruction SysCat)).pos ⊗ (bObj PortBoundary.empty).neg).P
      ((bObj PortBoundary.empty).pos ⊗ (𝟙_ (IntConstruction SysCat)).neg).P) :
    (⟨⟦A⟧⟩ : OpenTheory.Closed loopOpenTheory) = ⟨⟦B⟧⟩ ↔ Sys.StepEq A B := by
  constructor
  · intro h
    exact Quotient.exact (congrArg IntConstruction.Hom.hom h)
  · intro h
    exact IntConstruction.hom_ext (Quotient.sound h)

/-- Any two systems without events are step equivalent. -/
theorem stepEq_closed
    (A B : SysObj ((𝟙_ (IntConstruction SysCat)).pos ⊗ (bObj PortBoundary.empty).neg).P
      ((bObj PortBoundary.empty).pos ⊗ (𝟙_ (IntConstruction SysCat)).neg).P) :
    Sys.StepEq A B :=
  (closed_mk_eq_iff A B).1 (closed_eq _ _)

end CatCrypt.Crypto.UCLoopbackOpenTheory
