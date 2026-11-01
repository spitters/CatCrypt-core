/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.TransportAlong
public import CatCryptCore.Crypto.SDistrLift
public import CatCryptCore.Quantum.QRealizesMem
public import Mathlib.CategoryTheory.Monoidal.Transport

/-!
# The classical lift as a traced symmetric monoidal functor, and statistical transport

The category `PSysCat` of heap-independent classical reactive systems modulo step equivalence
(`CatCryptCore.Quantum.ClassicalLiftSys`) includes faithfully into `SysCat` by
`PSysCat.toSysCat`. Its traced symmetric monoidal structure (sums of ports, parallel
composition, the swap of the summands, the unbounded loopback) is induced along this inclusion:
the monoidal category by Mathlib's `Monoidal.induced`, the braiding by
`BraidedCategory.ofFaithful`, the symmetry by `SymmetricCategory.ofFaithful`, and the trace
axioms by the faithfulness of `toSysCat` from those of `SysCat.tracedCategory`.

The classical lift `liftFunctor R : PSysCat ⥤ QSysCat R` sends the tensor product of port types
to the tensor product on the nose, so it is a strong monoidal functor whose structure
isomorphisms are identities (`liftCoreMonoidal`). It sends the swap to the swap, so it is
braided, and it sends the trace to the trace (`liftFunctor_map_traceC`), in the form of a traced
monoidal functor: `F (Tr_U f) = Tr_{F U} (μ ≫ F f ≫ δ)`.

## Statistical transport

A classical realization of heap-independent systems at distance `ε` (`Realizes S I fun _ _ =>
ε`) bounds the statistical distance `sdistD` of their views from the empty heap by `ε`. The
lift of a distribution of views `liftDist` (the observation map of the observation-preserving
lift `liftObsPreserving`) is the diagonal subinstrument of the distribution, that is,
`classicalEmbed`, and the diamond distance of two such embeddings is at most the statistical
distance (`ClassicalDiamondLift.qdistDiamond_classicalEmbed_le`). Hence the quantum views of
the lifted systems are within diamond distance `ε`, with the same `ε`, against every
environment of the classical-lift form with heap-independent activations
(`quc_liftQSys_of_realizes_le`). The distance is statistical, so the numeric `ε` carries no
computational assumption.

Search words: classical lift, monoidal functor, braided functor, traced functor, statistical
transport, quantum UC, diamond norm.

## Main definitions

* `ClassicalLiftSys.PSysCat.homOfFun`, `ClassicalLiftSys.PSysCat.isoOfEquiv`.
* `ClassicalLiftSys.PSysCat.inducingData`: the data inducing the monoidal structure.
* Instances on `PSysCat`: `MonoidalCategory`, `BraidedCategory`, `SymmetricCategory`,
  `TracedCategory`; `PSysCat.toSysCat` is faithful, monoidal and braided.
* `ClassicalLiftSys.liftCoreMonoidal`: the strong monoidal structure of the classical lift;
  instances `(liftFunctor R).Monoidal` and `(liftFunctor R).Braided`.

## Main results

* `ClassicalLiftSys.PSysCat.toSysCat_map_trace`: the inclusion preserves the trace.
* `ClassicalLiftSys.liftFunctor_map_homOfFun`: the lift preserves forwarding systems.
* `ClassicalLiftSys.liftFunctor_map_traceC`: the lift preserves the trace.
* `ClassicalLiftSys.sdistD_heapFree_view_le`: a classical realization at distance `ε` bounds
  the statistical distance of the views from the empty heap.
* `ClassicalLiftSys.qdistDiamond_liftDist_le`: the observation map of `liftObsPreserving` does
  not increase distance from statistical to diamond distance.
* `ClassicalLiftSys.quc_liftQSys_of_realizes_le`: statistical transport of a realization at
  distance `ε` to the diamond-distance bound `ε` of the lifts.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Quantum.ClassicalLiftSys

open CategoryTheory MonoidalCategory
open CatCrypt.Crypto.UCTransparent CatCrypt.Quantum.ReactiveUC

/-! ## The traced symmetric monoidal structure of `PSysCat` -/

namespace PSysCat

/-- The inclusion of heap-independent systems in `SysCat` is faithful: step equivalence of
heap-independent systems is step equivalence of the underlying systems. -/
instance faithful_toSysCat : toSysCat.Faithful where
  map_injective {X Y} {f g} h := by
    induction f using Quotient.inductionOn with | h A =>
    induction g using Quotient.inductionOn with | h B =>
    have h' : (⟦A.1⟧ : Quotient (SysObj.stepSetoid X.P Y.P)) = ⟦B.1⟧ := h
    exact Quotient.sound (Quotient.exact h' :)

/-- Unfolding lemma of `toSysCat`: an object. -/
@[simp] theorem toSysCat_obj (X : PSysCat) : toSysCat.obj X = ⟨X.P⟩ :=
  rfl

/-- Unfolding lemma of the tensor product of `SysCat` on port types given by their ports. -/
@[simp] theorem _root_.CatCrypt.Crypto.UCTransparent.SysCat.mk_tensor (A B : Type) :
    (⟨A⟩ ⊗ ⟨B⟩ : SysCat) = ⟨A ⊕ B⟩ :=
  rfl

/-- Unfolding lemma of the unit of `SysCat`. -/
@[simp] theorem _root_.CatCrypt.Crypto.UCTransparent.SysCat.tensorUnit_eq :
    𝟙_ SysCat = ⟨Empty⟩ :=
  rfl

/-- The morphism given by a function of ports: the class of the stateless system
`Sys.ofFun f`. -/
noncomputable def homOfFun {X Y : PSysCat} (f : X.P → Y.P) : X ⟶ Y :=
  ⟦⟨⟨Unit, Sys.ofFun f⟩, heapPure_ofFun f⟩⟧

/-- Composition of morphisms given by functions is composition of the functions. -/
theorem homOfFun_comp {X Y Z : PSysCat} (f : X.P → Y.P) (g : Y.P → Z.P) :
    homOfFun f ≫ homOfFun g = homOfFun (g ∘ f) :=
  toSysCat.map_injective (by
    rw [toSysCat.map_comp]
    exact SysCat.homOfFun_comp (X := toSysCat.obj X) (Y := toSysCat.obj Y)
      (Z := toSysCat.obj Z) f g)

/-- The isomorphism of port types given by an equivalence of the ports. -/
noncomputable def isoOfEquiv {X Y : PSysCat} (e : X.P ≃ Y.P) : X ≅ Y where
  hom := homOfFun e
  inv := homOfFun e.symm
  hom_inv_id := by
    rw [homOfFun_comp, e.symm_comp_self]
    rfl
  inv_hom_id := by
    rw [homOfFun_comp, e.self_comp_symm]
    rfl

/-- The monoidal data: sums of ports, the parallel composition, the unit `Empty`, and the
structure isomorphisms of the sum equivalences. -/
noncomputable instance monoidalCategoryStruct : MonoidalCategoryStruct PSysCat where
  tensorObj X Y := ⟨X.P ⊕ Y.P⟩
  tensorHom := tensorHom
  whiskerLeft X _ _ g := tensorHom (𝟙 X) g
  whiskerRight f Y := tensorHom f (𝟙 Y)
  tensorUnit := ⟨Empty⟩
  associator X Y Z := isoOfEquiv (Equiv.sumAssoc X.P Y.P Z.P)
  leftUnitor X := isoOfEquiv (Equiv.emptySum Empty X.P)
  rightUnitor X := isoOfEquiv (Equiv.sumEmpty X.P Empty)

/-- Unfolding lemma of the tensor product of objects: the sum of the ports. -/
@[simp] theorem tensorObj_P (X Y : PSysCat) : (X ⊗ Y).P = (X.P ⊕ Y.P) :=
  rfl

/-- Unfolding lemma of the unit: no ports. -/
@[simp] theorem tensorUnit_P : (𝟙_ PSysCat).P = Empty :=
  rfl

/-- The inclusion preserves the tensor product of morphisms. -/
theorem toSysCat_map_tensorHom {X₁ Y₁ X₂ Y₂ : PSysCat} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    toSysCat.map (f ⊗ₘ g) = toSysCat.map f ⊗ₘ toSysCat.map g := by
  induction f using Quotient.inductionOn
  induction g using Quotient.inductionOn
  rfl

/-- The data inducing the monoidal structure of `PSysCat` along the inclusion in `SysCat`:
the tensor products agree on the nose. -/
noncomputable def inducingData : Monoidal.InducingFunctorData toSysCat where
  μIso _ _ := Iso.refl _
  whiskerLeft_eq X _ _ f := by
    dsimp only [toSysCat_obj, tensorObj_P, SysCat.mk_tensor]
    simp only [Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id]
    exact toSysCat_map_tensorHom (𝟙 X) f
  whiskerRight_eq f Y := by
    dsimp only [toSysCat_obj, tensorObj_P, SysCat.mk_tensor]
    simp only [Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id]
    exact toSysCat_map_tensorHom f (𝟙 Y)
  tensorHom_eq f g := by
    dsimp only [toSysCat_obj, tensorObj_P, SysCat.mk_tensor]
    simp only [Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id]
    exact toSysCat_map_tensorHom f g
  εIso := Iso.refl _
  associator_eq X Y Z := by
    dsimp only [toSysCat_obj, tensorObj_P, SysCat.mk_tensor]
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.refl_hom, Iso.refl_inv, tensorIso_hom,
      id_tensorHom_id, Category.id_comp]
    erw [Category.id_comp, Category.id_comp, Category.comp_id]
    rfl
  leftUnitor_eq X := by
    dsimp only [toSysCat_obj, tensorObj_P, tensorUnit_P, SysCat.mk_tensor, SysCat.tensorUnit_eq]
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.refl_hom, Iso.refl_inv, tensorIso_hom,
      id_tensorHom_id, Category.id_comp]
    exact (Category.id_comp _).symm
  rightUnitor_eq X := by
    dsimp only [toSysCat_obj, tensorObj_P, tensorUnit_P, SysCat.mk_tensor, SysCat.tensorUnit_eq]
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.refl_hom, Iso.refl_inv, tensorIso_hom,
      id_tensorHom_id, Category.id_comp]
    exact (Category.id_comp _).symm

/-- `PSysCat` is a monoidal category under the parallel composition, induced along the
inclusion in `SysCat`. -/
noncomputable instance monoidalCategory : MonoidalCategory PSysCat :=
  Monoidal.induced toSysCat inducingData

/-- The inclusion in `SysCat` is a strong monoidal functor with identity structure maps. -/
noncomputable instance toSysCat_monoidal : toSysCat.Monoidal :=
  Monoidal.fromInducedMonoidal toSysCat inducingData

/-- `PSysCat` is braided by the swap of the summands. -/
noncomputable instance braidedCategory : BraidedCategory PSysCat :=
  .ofFaithful toSysCat
    (fun X Y => isoOfEquiv (X := X ⊗ Y) (Y := Y ⊗ X) (Equiv.sumComm X.P Y.P))
    fun _ _ => (Category.id_comp _).trans (Category.comp_id _).symm

/-- The inclusion in `SysCat` is braided. -/
noncomputable instance toSysCat_braided : toSysCat.Braided where
  braided _ _ := (Category.id_comp _).trans (Category.comp_id _).symm

/-- `PSysCat` is a symmetric monoidal category. -/
noncomputable instance symmetricCategory : SymmetricCategory PSysCat :=
  .ofFaithful toSysCat

/-- The inclusion sends the unbounded loopback of `PSysCat` to the trace of `SysCat`. -/
theorem toSysCat_map_trace (U : PSysCat) {X Y : PSysCat} (f : X ⊗ U ⟶ Y ⊗ U) :
    toSysCat.map (trace U f) = TracedCategory.trace (toSysCat.obj U) (toSysCat.map f) := by
  induction f using Quotient.inductionOn
  rfl

/-- `PSysCat` is a traced symmetric monoidal category; the trace is the unbounded loopback.
Each axiom holds after the faithful inclusion in `SysCat`. -/
noncomputable instance tracedCategory : TracedCategory PSysCat where
  trace := trace
  trace_whiskerRight_comp U _ _ _ g f := by
    induction g using Quotient.inductionOn
    induction f using Quotient.inductionOn
    exact Quotient.sound (Sys.loopbackω_seq_left _ _).stepEq
  trace_comp_whiskerRight U _ _ _ f h := by
    induction f using Quotient.inductionOn
    induction h using Quotient.inductionOn
    exact Quotient.sound (Sys.loopbackω_seq_right _ _).stepEq
  trace_whiskerLeft_comp g f := by
    induction g using Quotient.inductionOn
    induction f using Quotient.inductionOn
    exact Quotient.sound (Relation.EqvGen.symm _ _ (Sys.loopbackω_slide _ _).stepEq)
  trace_tensorUnit f := by
    induction f using Quotient.inductionOn
    exact Quotient.sound (Sys.loopbackω_empty _).stepEq
  trace_tensor U V _ _ f := by
    induction f using Quotient.inductionOn with
    | h A =>
      refine Quotient.sound (Relation.EqvGen.trans _ _ _
        (Relation.EqvGen.symm _ _ (Sys.loopbackω_loopbackω A.1.sys).stepEq)
        (Relation.EqvGen.symm _ _ (Sys.StepEq.loopbackω (Sys.StepEq.loopbackω
          (Sys.StepMapOn.ofFun_seq_seq_ofFun _ A.1.sys _).stepEq))))
  whiskerLeft_trace W U _ _ f := by
    induction f using Quotient.inductionOn with
    | h A =>
      refine Quotient.sound (Relation.EqvGen.trans _ _ _
        (Sys.loopbackω_par_left (W := W.P) A.1.sys).stepEq
        (Relation.EqvGen.symm _ _ (Sys.StepEq.loopbackω
          (Sys.StepMapOn.ofFun_seq_seq_ofFun _ ((Sys.ofFun id).par A.1.sys) _).stepEq)))
  trace_braiding U := Quotient.sound (Sys.loopbackω_swap (X := U.P)).stepEq

end PSysCat

/-! ## The classical lift as a traced symmetric monoidal functor -/

section Functor

variable (R : Type) [Fintype R]

/-- The lift sends the morphism of a function to the morphism of the function. -/
theorem liftFunctor_map_homOfFun {X Y : PSysCat} (f : X.P → Y.P) :
    (liftFunctor R).map (PSysCat.homOfFun f) =
      QSysCat.homOfFun (X := (liftFunctor R).obj X) (Y := (liftFunctor R).obj Y) f :=
  Quotient.sound (by
    change QRSys.StepEq ⟨Unit, liftSys (Sys.ofFun f)⟩ ⟨Unit, QRSys.ofFun f⟩
    rw [liftSys_ofFun]
    exact Relation.EqvGen.refl _)

/-- The lift commutes with right whiskering. -/
theorem liftFunctor_map_whiskerRight {X Y : PSysCat} (f : X ⟶ Y) (Z : PSysCat) :
    (liftFunctor R).map (f ▷ Z) = (liftFunctor R).map f ▷ (liftFunctor R).obj Z := by
  refine (liftFunctor_map_tensor f (𝟙 Z)).trans ?_
  rw [(liftFunctor R).map_id]
  rfl

/-- The lift commutes with left whiskering. -/
theorem liftFunctor_map_whiskerLeft (X : PSysCat) {Y Z : PSysCat} (g : Y ⟶ Z) :
    (liftFunctor R).map (X ◁ g) = (liftFunctor R).obj X ◁ (liftFunctor R).map g := by
  refine (liftFunctor_map_tensor (𝟙 X) g).trans ?_
  rw [(liftFunctor R).map_id]
  rfl

/-- The strong monoidal structure of the classical lift: the tensor products agree on the nose,
so the structure isomorphisms are identities. -/
noncomputable def liftCoreMonoidal : (liftFunctor R).CoreMonoidal where
  εIso := Iso.refl _
  μIso _ _ := Iso.refl _
  μIso_hom_natural_left f X' := (Category.comp_id _).trans
    ((liftFunctor_map_whiskerRight R f X').symm.trans (Category.id_comp _).symm)
  μIso_hom_natural_right X' f := (Category.comp_id _).trans
    ((liftFunctor_map_whiskerLeft R X' f).symm.trans (Category.id_comp _).symm)
  associativity X Y Z := by
    erw [id_whiskerRight, Category.id_comp, Category.id_comp, MonoidalCategory.whiskerLeft_id,
      Category.id_comp, Category.comp_id]
    exact liftFunctor_map_homOfFun R (Equiv.sumAssoc X.P Y.P Z.P)
  left_unitality X := by
    erw [id_whiskerRight, Category.id_comp, Category.id_comp]
    exact (liftFunctor_map_homOfFun R (Equiv.emptySum Empty X.P)).symm
  right_unitality X := by
    erw [MonoidalCategory.whiskerLeft_id, Category.id_comp, Category.id_comp]
    exact (liftFunctor_map_homOfFun R (Equiv.sumEmpty X.P Empty)).symm

/-- The classical lift is a strong monoidal functor. -/
noncomputable instance liftFunctor_monoidal : (liftFunctor R).Monoidal :=
  (liftCoreMonoidal R).toMonoidal

/-- The tensorator of the classical lift is the identity. -/
theorem liftFunctor_μ (X Y : PSysCat) : Functor.LaxMonoidal.μ (liftFunctor R) X Y = 𝟙 _ :=
  rfl

/-- The inverse tensorator of the classical lift is the identity. -/
theorem liftFunctor_δ (X Y : PSysCat) : Functor.OplaxMonoidal.δ (liftFunctor R) X Y = 𝟙 _ :=
  rfl

/-- The classical lift is a braided (hence symmetric) monoidal functor: it sends the swap of
the summands to the swap. -/
noncomputable instance liftFunctor_braided : (liftFunctor R).Braided where
  braided X Y := (Category.id_comp _).trans
    ((liftFunctor_map_homOfFun R (Equiv.sumComm X.P Y.P)).trans (Category.comp_id _).symm)

/-- **The trace.** The classical lift is a traced monoidal functor: the lift of the trace of
`f` over `U` is the trace over the lift of `U` of the lift of `f`, conjugated by the structure
maps of the functor. -/
theorem liftFunctor_map_traceC (U : PSysCat) {X Y : PSysCat} (f : X ⊗ U ⟶ Y ⊗ U) :
    (liftFunctor R).map (TracedCategory.trace U f) =
      TracedCategory.trace ((liftFunctor R).obj U)
        (Functor.LaxMonoidal.μ (liftFunctor R) X U ≫ (liftFunctor R).map f ≫
          Functor.OplaxMonoidal.δ (liftFunctor R) Y U) := by
  have h : Functor.LaxMonoidal.μ (liftFunctor R) X U ≫ (liftFunctor R).map f ≫
      Functor.OplaxMonoidal.δ (liftFunctor R) Y U = (liftFunctor R).map f :=
    (Category.id_comp _).trans (Category.comp_id _)
  rw [h]
  exact liftFunctor_map_trace U f

end Functor

/-! ## Statistical transport -/

section Statistical

open CatCrypt.Core CatCrypt.Prob
open CatCrypt.Crypto.UCMonad.DiamondNorm UCMonad.SDistrUC
open CatCrypt.Crypto.SDistrLift CatCrypt.Crypto.UCTransport
open CatCrypt.Crypto.UCConcrete (Env)
open _root_.Quantum (SubInstrument)
open _root_.Quantum.SubInstrument (ofSDistr)
open scoped ENNReal

variable {τ υ E O ζ α β : Type} {d : ℕ}

/-- Running a computation from the empty heap and continuing with heap-independent samples is
continuing the sub-distribution of its results. -/
theorem heapFree_bind_sdistrToSPComp (c : SPComp α) (D : α → SDistr β) :
    heapFree (c.bind fun a => sdistrToSPComp (D a)) = (heapFree c).bind D := by
  simp only [heapFree, SPComp.bind_def, sdistrToSPComp_run, SDistr.bind_assoc, SDistr.pure_bind,
    SDistr.bind_pure]

/-- **Statistical distance of the views.** A classical realization at distance `ε` bounds the
statistical distance of the views from the empty heap by `ε`, for every family of
environments. -/
theorem sdistD_heapFree_view_le {S : Sys τ E O} {I : Sys υ E O} {ε : ℝ≥0∞}
    (h : Realizes S I fun _ _ => ε) (Zs : α → Strat ζ E O) :
    sdistD (fun a => heapFree (view S (Zs a))) (fun a => heapFree (view I (Zs a))) ≤ ε := by
  refine iSup₂_le fun D a => ?_
  have hg := h ζ ⟨Zs a, Heap.empty, fun z => sdistrToSPComp (D z)⟩
  simp only [Env.gap, prTrue_eq_heapFree, heapFree_bind_sdistrToSPComp] at hg
  exact hg

/-- Relabelling the register of a diagonal subinstrument gives the diagonal subinstrument. -/
theorem relabel_ofSDistr {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B) (μ : SDistr α) :
    relabel e (ofSDistr μ : SubInstrument A A α) = ofSDistr μ := by
  refine _root_.Quantum.DSubInstrument.ext (funext fun a => LinearMap.ext fun ρ => ?_)
  rw [relabel_branch, reindexMap_apply]
  ext x y
  simp

/-- The observation map of the lift is the diagonal subinstrument of the distribution. -/
theorem liftDist_eq (μ : SDistr ζ) : liftDist d μ = ofSDistr μ := by
  have key := appendBasis_unit_discard (A := Fin d) (ofSDistr μ) fun z => SubInstrument.pure z
  rw [relabel_ofSDistr, SubInstrument.bind_pure] at key
  exact key

/-- As a quantum computation, the lift of a distribution is its classical embedding. -/
theorem liftDist_toQComp (μ : SDistr ζ) : (liftDist d μ).toQComp = classicalEmbed μ := by
  rw [liftDist_eq, ofSDistr_eq_mk', CPComp.toQComp_mk']

/-- **The observation map is statistical-to-diamond contracting.** The diamond distance of the
lifts of two families of distributions is at most their statistical distance. -/
theorem qdistDiamond_liftDist_le [NeZero d] (f g : α → SDistr ζ) :
    qdistDiamond (fun a => (liftDist d (f a)).toQComp) (fun a => (liftDist d (g a)).toQComp)
        (fun a => CPComp.branch_cp (liftDist d (f a)))
        (fun a => CPComp.branch_cp (liftDist d (g a))) ≤ sdistD f g := by
  have hf : (fun a => (liftDist d (f a)).toQComp) = fun a => classicalEmbed (f a) :=
    funext fun a => liftDist_toQComp (f a)
  have hg : (fun a => (liftDist d (g a)).toQComp) = fun a => classicalEmbed (g a) :=
    funext fun a => liftDist_toQComp (g a)
  exact quc_congr _ _ (ClassicalDiamondLift.qdistDiamond_classicalEmbed_le f g) hf.symm hg.symm

/-- The view of a lifted environment against a lifted heap-independent system, as a quantum
computation, is the classical embedding of the classical view from the empty heap; the
cascade of the observation-preserving lift `liftObsPreserving`. -/
theorem qview_liftQSys_toQComp {S : Sys τ E O} (hS : S.HeapPure)
    (Z : {Z : Strat ζ E O // StratPure Z}) :
    (qview (liftQSys (d := d) S) (liftStrat Z.1)).toQComp =
      classicalEmbed (heapFree (view S Z.1)) := by
  rw [qview_liftQSys hS Z.2]
  exact liftDist_toQComp _

/-- **Statistical transport.** A classical realization at distance `ε` between heap-independent
systems gives the bound `ε`, in the diamond norm, between the quantum views of their lifts
against every environment of the classical-lift form with heap-independent activations. -/
theorem quc_liftQSys_of_realizes_le [NeZero d] {S : Sys τ E O} {I : Sys υ E O}
    (hS : S.HeapPure) (hI : I.HeapPure) {ε : ℝ≥0∞} (h : Realizes S I fun _ _ => ε)
    (ζ : Type) :
    QUCEmulatesDiamond ε
      (fun Z : {Z : Strat ζ E O // StratPure Z} =>
        (qview (liftQSys (d := d) S) (liftStrat Z.1)).toQComp)
      (fun Z => (qview (liftQSys I) (liftStrat Z.1)).toQComp)
      (fun Z => CPComp.branch_cp (qview (liftQSys S) (liftStrat Z.1)))
      (fun Z => CPComp.branch_cp (qview (liftQSys I) (liftStrat Z.1))) :=
  quc_congr _ _
    (ClassicalDiamondLift.classical_to_quantum_diamond_lift _ _
      (sdistD_heapFree_view_le h Subtype.val))
    (funext fun Z => (qview_liftQSys_toQComp hS Z).symm)
    (funext fun Z => (qview_liftQSys_toQComp hI Z).symm)

end Statistical

end CatCrypt.Quantum.ClassicalLiftSys
