/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCLoopbackTrace
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# The symmetric monoidal structure on the category of port types

The category `SysCat` of port types, with systems modulo step equivalence as morphisms, is
symmetric monoidal. The tensor product of port types is their sum and the tensor product of
morphisms is the parallel composition `Sys.par`; the unit is `Empty`. The associator, the
unitors and the braiding are the classes of the stateless systems `Sys.ofFun` of
`Equiv.sumAssoc`, `Equiv.emptySum`, `Equiv.sumEmpty` and `Equiv.sumComm`.

Every law is a step equivalence given by one step map on the trivial invariant: the
interchange of `seq` and `par` and the naturality of the structure maps reassociate the states,
and the coherence laws relate stateless systems that compute the same function of the events.

## Main definitions

* `SysCat.homOfFun f`: the class of the stateless system `Sys.ofFun f`.
* `SysCat.isoOfEquiv e`: the isomorphism of port types given by an equivalence.
* `SysCat.monoidalCategory`, `SysCat.symmetricCategory`.

## Main results

* `Sys.StepMapOn.seq_par`: the interchange of the cascade and the parallel composition.
* `Sys.StepMapOn.par_assoc_seq`, `Sys.StepMapOn.par_swap_seq`: naturality of the associator and
  of the symmetry.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CategoryTheory MonoidalCategory

namespace Sys

variable {τ υ τ' υ' ρ E O P E' O' P' E'' : Type}

/-- A state map that commutes with every step is a step map on the trivial invariant. -/
theorem StepMapOn.of_step {R : Sys τ E O} {I : Sys υ E O} (f : τ → υ)
    (hinit : f R.init = I.init)
    (hstep : ∀ t e, SPComp.map (fun p => (f p.1, p.2)) (R.step t e) = I.step (f t) e) :
    StepMapOn R I (fun _ => True) f :=
  ⟨trivial, hinit, fun _ _ _ _ _ => trivial, fun t e _ => hstep t e⟩

/-- The cascade of two stateless systems is the stateless system of the composite. -/
theorem StepMapOn.ofFun_seq (f : E → O) (g : O → P) :
    StepMapOn ((ofFun f).seq (ofFun g)) (ofFun (g ∘ f)) (fun _ => True) (fun _ => ()) :=
  StepMapOn.of_step _ rfl fun _ _ => by simp [seq_step, ofFun]

/-- The parallel composition of two stateless systems is the stateless system of the sum of
the functions. -/
theorem StepMapOn.ofFun_par (f : E → O) (g : E' → O') :
    StepMapOn ((ofFun f).par (ofFun g)) (ofFun (Sum.map f g)) (fun _ => True) (fun _ => ()) :=
  StepMapOn.of_step _ rfl fun _ e => by rcases e with e | e <;> simp [ofFun]

/-- **Interchange.** The parallel composition of two cascades is the cascade of the parallel
compositions; the state map exchanges the middle components. -/
theorem StepMapOn.seq_par (S : Sys τ E O) (T : Sys υ O P) (S' : Sys τ' E' O')
    (T' : Sys υ' O' P') :
    StepMapOn ((S.seq T).par (S'.seq T')) ((S.par S').seq (T.par T')) (fun _ => True)
      (fun s => ((s.1.1, s.2.1), (s.1.2, s.2.2))) :=
  StepMapOn.of_step _ rfl fun s e => by
    rcases e with e | e <;> simp [seq_step, SPComp.map]

/-- **Naturality of the associator.** Reassociating the states is a step map from the
reassociation after the parallel composition to the reassociation before it. -/
theorem StepMapOn.par_assoc_seq (S : Sys τ E O) (T : Sys υ E' O') (U : Sys ρ E'' P) :
    StepMapOn (((S.par T).par U).seq (ofFun (Equiv.sumAssoc O O' P)))
      ((ofFun (Equiv.sumAssoc E E' E'')).seq (S.par (T.par U))) (fun _ => True)
      (fun s => ((), (s.1.1.1, (s.1.1.2, s.1.2)))) :=
  StepMapOn.of_step _ rfl fun s e => by
    rcases e with (e | e) | e <;> simp [seq_step, ofFun, SPComp.map]

/-- **Naturality of the symmetry.** Exchanging the states is a step map from the swap after the
parallel composition to the swap before the exchanged parallel composition. -/
theorem StepMapOn.par_swap_seq (S : Sys τ E O) (T : Sys υ E' O') :
    StepMapOn ((S.par T).seq (ofFun (Equiv.sumComm O O')))
      ((ofFun (Equiv.sumComm E E')).seq (T.par S)) (fun _ => True)
      (fun s => ((), (s.1.2, s.1.1))) :=
  StepMapOn.of_step _ rfl fun s e => by
    rcases e with e | e <;> simp [seq_step, ofFun, SPComp.map]

/-- **Naturality of the left unitor.** -/
theorem StepMapOn.empty_par_seq (S : Sys τ E O) :
    StepMapOn (((ofFun (id : Empty → Empty)).par S).seq (ofFun (Equiv.emptySum Empty O)))
      ((ofFun (Equiv.emptySum Empty E)).seq S) (fun _ => True) (fun s => ((), s.1.2)) :=
  StepMapOn.of_step _ rfl fun s e => by
    rcases e with e | e
    · exact e.elim
    · simp [seq_step, ofFun, SPComp.map]

/-- **Naturality of the right unitor.** -/
theorem StepMapOn.par_empty_seq (S : Sys τ E O) :
    StepMapOn ((S.par (ofFun (id : Empty → Empty))).seq (ofFun (Equiv.sumEmpty O Empty)))
      ((ofFun (Equiv.sumEmpty E Empty)).seq S) (fun _ => True) (fun s => ((), s.1.1)) :=
  StepMapOn.of_step _ rfl fun s e => by
    rcases e with e | e
    · simp [seq_step, ofFun, SPComp.map]
    · exact e.elim

end Sys

namespace SysCat

/-- The morphism given by a function of ports: the class of the stateless system
`Sys.ofFun f`. -/
noncomputable def homOfFun {X Y : SysCat} (f : X.P → Y.P) : X ⟶ Y :=
  ⟦⟨Unit, Sys.ofFun f⟩⟧

/-- Composition of morphisms given by functions is composition of the functions. -/
theorem homOfFun_comp {X Y Z : SysCat} (f : X.P → Y.P) (g : Y.P → Z.P) :
    homOfFun f ≫ homOfFun g = homOfFun (g ∘ f) :=
  Quotient.sound (Sys.StepMapOn.ofFun_seq f g).stepEq

/-- The isomorphism of port types given by an equivalence of the ports. -/
noncomputable def isoOfEquiv {X Y : SysCat} (e : X.P ≃ Y.P) : X ≅ Y where
  hom := homOfFun e
  inv := homOfFun e.symm
  hom_inv_id := by
    rw [homOfFun_comp, e.symm_comp_self]
    rfl
  inv_hom_id := by
    rw [homOfFun_comp, e.self_comp_symm]
    rfl

/-- Unfolding lemma of `isoOfEquiv`: the forward morphism. -/
theorem isoOfEquiv_hom {X Y : SysCat} (e : X.P ≃ Y.P) : (isoOfEquiv e).hom = homOfFun e :=
  rfl

/-- Unfolding lemma of `isoOfEquiv`: the backward morphism. -/
theorem isoOfEquiv_inv {X Y : SysCat} (e : X.P ≃ Y.P) : (isoOfEquiv e).inv = homOfFun e.symm :=
  rfl

/-- The tensor product of morphisms: the parallel composition. -/
noncomputable def tensorHom {X₁ Y₁ X₂ Y₂ : SysCat} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (⟨X₁.P ⊕ X₂.P⟩ : SysCat) ⟶ ⟨Y₁.P ⊕ Y₂.P⟩ :=
  Quotient.map₂ SysObj.par (fun _ _ h₁ _ _ h₂ => Sys.StepEq.par h₁ h₂) f g

/-- **Interchange.** The tensor product of morphisms commutes with composition. -/
theorem tensorHom_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : SysCat} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ = tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) := by
  induction f₁ using Quotient.inductionOn
  induction f₂ using Quotient.inductionOn
  induction g₁ using Quotient.inductionOn
  induction g₂ using Quotient.inductionOn
  refine (Quotient.sound ?_).symm
  exact (Sys.StepMapOn.seq_par _ _ _ _).stepEq

/-- The tensor product of morphisms given by functions is given by the sum of the functions. -/
theorem homOfFun_tensorHom {X₁ Y₁ X₂ Y₂ : SysCat} (f : X₁.P → Y₁.P) (g : X₂.P → Y₂.P) :
    tensorHom (homOfFun f) (homOfFun g) = homOfFun (X := ⟨X₁.P ⊕ X₂.P⟩) (Y := ⟨Y₁.P ⊕ Y₂.P⟩)
      (Sum.map f g) :=
  Quotient.sound (Sys.StepMapOn.ofFun_par f g).stepEq

/-- The monoidal data: sums of ports, the parallel composition, the unit `Empty`, and the
structure isomorphisms of the sum equivalences. -/
noncomputable instance monoidalCategoryStruct : MonoidalCategoryStruct SysCat where
  tensorObj X Y := ⟨X.P ⊕ Y.P⟩
  tensorHom := tensorHom
  whiskerLeft X _ _ g := tensorHom (𝟙 X) g
  whiskerRight f Y := tensorHom f (𝟙 Y)
  tensorUnit := ⟨Empty⟩
  associator X Y Z := isoOfEquiv (Equiv.sumAssoc X.P Y.P Z.P)
  leftUnitor X := isoOfEquiv (Equiv.emptySum Empty X.P)
  rightUnitor X := isoOfEquiv (Equiv.sumEmpty X.P Empty)

/-- Unfolding lemma of the identity: the morphism of the identity function. -/
theorem id_eq_homOfFun (X : SysCat) : 𝟙 X = homOfFun id :=
  rfl

/-- Unfolding lemma of the associator. -/
theorem associator_def (X Y Z : SysCat) :
    α_ X Y Z = isoOfEquiv (X := (X ⊗ Y) ⊗ Z) (Y := X ⊗ (Y ⊗ Z)) (Equiv.sumAssoc X.P Y.P Z.P) :=
  rfl

/-- Unfolding lemma of the left unitor. -/
theorem leftUnitor_def (X : SysCat) :
    λ_ X = isoOfEquiv (X := 𝟙_ SysCat ⊗ X) (Y := X) (Equiv.emptySum Empty X.P) :=
  rfl

/-- Unfolding lemma of the right unitor. -/
theorem rightUnitor_def (X : SysCat) :
    ρ_ X = isoOfEquiv (X := X ⊗ 𝟙_ SysCat) (Y := X) (Equiv.sumEmpty X.P Empty) :=
  rfl

/-- Whiskering a morphism given by a function on the left. -/
theorem whiskerLeft_homOfFun (X : SysCat) {Y Z : SysCat} (g : Y.P → Z.P) :
    X ◁ homOfFun g = homOfFun (X := X ⊗ Y) (Y := X ⊗ Z) (Sum.map id g) :=
  homOfFun_tensorHom id g

/-- Whiskering a morphism given by a function on the right. -/
theorem whiskerRight_homOfFun {X Y : SysCat} (f : X.P → Y.P) (Z : SysCat) :
    homOfFun f ▷ Z = homOfFun (X := X ⊗ Z) (Y := Y ⊗ Z) (Sum.map f id) :=
  homOfFun_tensorHom f id

/-- `SysCat` is a monoidal category under the parallel composition. -/
noncomputable instance monoidalCategory : MonoidalCategory SysCat where
  toMonoidalCategoryStruct := monoidalCategoryStruct
  tensorHom_def f g := by
    change tensorHom f g = tensorHom f (𝟙 _) ≫ tensorHom (𝟙 _) g
    rw [tensorHom_comp, Category.comp_id, Category.id_comp]
  id_tensorHom_id _ _ := by
    change tensorHom (homOfFun id) (homOfFun id) = homOfFun id
    rw [homOfFun_tensorHom, Sum.map_id_id]
  tensorHom_comp_tensorHom := tensorHom_comp
  whiskerLeft_id _ _ := by
    change tensorHom (homOfFun id) (homOfFun id) = homOfFun id
    rw [homOfFun_tensorHom, Sum.map_id_id]
  id_whiskerRight _ _ := by
    change tensorHom (homOfFun id) (homOfFun id) = homOfFun id
    rw [homOfFun_tensorHom, Sum.map_id_id]
  associator_naturality := by
    rintro _ _ _ _ _ _ ⟨A⟩ ⟨B⟩ ⟨C⟩
    refine Quotient.sound ?_
    exact (Sys.StepMapOn.par_assoc_seq A.sys B.sys C.sys).stepEq
  leftUnitor_naturality := by
    rintro _ _ ⟨A⟩
    refine Quotient.sound ?_
    exact (Sys.StepMapOn.empty_par_seq A.sys).stepEq
  rightUnitor_naturality := by
    rintro _ _ ⟨A⟩
    refine Quotient.sound ?_
    exact (Sys.StepMapOn.par_empty_seq A.sys).stepEq
  pentagon _ _ _ _ := by
    simp only [associator_def, isoOfEquiv_hom, whiskerLeft_homOfFun, whiskerRight_homOfFun,
      homOfFun_comp]
    congr 1
    funext e
    rcases e with ((e | e) | e) | e <;> rfl
  triangle _ _ := by
    simp only [associator_def, leftUnitor_def, rightUnitor_def, isoOfEquiv_hom,
      whiskerLeft_homOfFun, whiskerRight_homOfFun, homOfFun_comp]
    congr 1
    funext e
    rcases e with (e | e) | e
    · rfl
    · exact e.elim
    · rfl

/-- `SysCat` is a symmetric monoidal category; the symmetry swaps the summands. -/
noncomputable instance symmetricCategory : SymmetricCategory SysCat where
  braiding X Y := isoOfEquiv (X := ⟨X.P ⊕ Y.P⟩) (Y := ⟨Y.P ⊕ X.P⟩) (Equiv.sumComm X.P Y.P)
  braiding_naturality_right := by
    rintro _ _ _ ⟨A⟩
    refine Quotient.sound ?_
    exact (Sys.StepMapOn.par_swap_seq (Sys.ofFun id) A.sys).stepEq
  braiding_naturality_left := by
    rintro _ _ ⟨A⟩ _
    refine Quotient.sound ?_
    exact (Sys.StepMapOn.par_swap_seq A.sys (Sys.ofFun id)).stepEq
  hexagon_forward _ _ _ := by
    simp only [associator_def, isoOfEquiv_hom, whiskerLeft_homOfFun, whiskerRight_homOfFun,
      homOfFun_comp]
    congr 1
    funext e
    rcases e with (e | e) | e <;> rfl
  hexagon_reverse _ _ _ := by
    simp only [associator_def, isoOfEquiv_hom, isoOfEquiv_inv, whiskerLeft_homOfFun,
      whiskerRight_homOfFun, homOfFun_comp]
    congr 1
    funext e
    rcases e with e | e | e <;> rfl
  symmetry _ _ := by
    simp only [isoOfEquiv_hom, homOfFun_comp, id_eq_homOfFun]
    congr 1
    funext e
    rcases e with e | e <;> rfl

end SysCat

end CatCrypt.Crypto.UCTransparent
