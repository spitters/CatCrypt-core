/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Bridges.IrisBridge.WPMonadBI
public import RefinementWP.Step

/-!
# The separating refinement weakest precondition `swrp`

`swrp γ c a Q` is the assertion `∀ Qa, γ (a Qa) -∗ wp c (fun v => ∃ w, Q v w ∗ γ (Qa w))` in a
BI `Ω`. It is the formula of `RefinementWP.wrp` with the residual of `∗` in place of the Heyting
implication and `∗` in place of the meet. The concrete program `c` has a weakest precondition in
`Ω` (`WPMonadBI`). The abstract side is a predicate transformer `a : (β → A) → A` on any type
`A` of abstract assertions, and the concretization is a map `γ : A → Ω`. No rule needs an order
on `A` or monotonicity of `a`.

At `HProp` the concrete weakest precondition is `slWP`, which is of partial correctness: it
constrains the outcomes in the support of `c`, and `slWP_fail` holds at every postcondition, so
`swrp` refinement is partial-correctness refinement.

## Main results

### The generic rules

The section `Generic` uses of the BI only the preorder `⊢`, monotonicity, symmetry and
associativity of `∗`, the adjunction of `∗` and `-∗`, and the rules of `∀` and `∃`. Of the
concrete weakest precondition it uses monotonicity, the laws of `pure` and `bind`, and, for the
two frame rules, `WPFrameBI`.

* `swrp_intro`, `swrp_transport`: the wand adjunction.
* `swrp_mono`, `swrp_mono_abstract`: consequence.
* `swrp_bind`, `swrp_bind_rule`: sequencing, when the abstract sequence `ab` satisfies
  `γ (ab Qb) ⊢ γ (a (fun w => g w Qb))`. This is the converse of `WPMonadBI.wp_bind` seen
  through `γ`.
* `swrp_frame`, `swrp_frame_conc`: a resource is framed into the return relation or into the
  concretization.
* `swrp_vcomp`: vertical pasting. The outer concretization `γ₂` is monotone and preserves
  suprema. It is lax monoidal at the inner precondition, which moves that precondition inside
  `γ₂`, and oplax monoidal at the inner return relation, which moves that relation out of `γ₂`.

### Rules with the unit and embedded propositions

* `emp_entails_swrp_iff`: closed refinement is the lax square.
* `swrp_refl`: reflexivity.
* `swrp_vcomp_pure`: pasting of closed refinements with a heap-independent inner return
  relation needs only that `γ₂` is monotone and preserves suprema.
* `swrp_biEntails_of_sep_and`: where `∗` is `∧`, `swrp` is the cartesian residual.

### At `HProp` and `slWP`

* `swrp_vcomp_reindex`: renamings of locations satisfy the hypotheses of pasting.
* `emp_entails_swrp_iff_refines`: at heap-independent return relations, closed `swrp`
  refinement is `RefinementWP.Refines` at `top`, for every concretization.
* `refines_of_entails_swrp`: under a persistent precondition `swrp` refinement gives `Refines`.
* `swrp_entails_wrp`: at a persistent concretization `swrp` entails `RefinementWP.wrp`.
* `swrp_set_framed`: the refinement of a write to one location, framed past another location.

## References

* S. Graf, distillery, for `wrp`.
* D. Frumin, R. Krebbers, L. Birkedal, *ReLoC: A Mechanised Relational Logic for Fine-Grained
  Concurrency*, LICS 2018, for refinement as a wand into a weakest precondition.

## Search words

separation logic, refinement weakest precondition, wrp, frame rule, data refinement, residual,
magic wand, vertical pasting, lax monoidal, oplax monoidal
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.IrisBridge

open Iris.BI

universe u u' u'' v v' w w' w''

/-! ## Definition and rules over a BI -/

section Generic

variable {M : Type u → Type v} {Ω : Type w} [Iris.BI Ω] [Monad M] [WPMonadBI M Ω]
  {α α' : Type u} {A : Type w'} {β β' : Type u'}

/-- The concrete postcondition of the return relation `Q` and the abstract postcondition `Qa`:
at `v` it is `∃ w, Q v w ∗ γ (Qa w)`. -/
def swrpPost (γ : A → Ω) (Q : α → β → Ω) (Qa : β → A) : α → Ω :=
  fun v => iprop(∃ w, Q v w ∗ γ (Qa w))

/-- The separating refinement weakest precondition: the resource that turns each weakest
precondition of the abstract transformer `a`, seen through `γ`, into a weakest precondition of
the concrete program `c`. -/
def swrp (γ : A → Ω) (c : M α) (a : (β → A) → A) (Q : α → β → Ω) : Ω :=
  iprop(∀ Qa, γ (a Qa) -∗ WPMonadBI.wp c (swrpPost γ Q Qa))

variable {γ : A → Ω} {c : M α} {a : (β → A) → A} {Q Q' : α → β → Ω} {P : Ω}

/-- Introduction: `P` entails `swrp` when `P` separated from each concretized abstract
precondition entails the concrete precondition. -/
theorem swrp_intro (h : ∀ Qa, P ∗ γ (a Qa) ⊢ WPMonadBI.wp c (swrpPost γ Q Qa)) :
    P ⊢ swrp γ c a Q :=
  forall_intro fun Qa => wand_intro (h Qa)

/-- Transport: under `P ⊢ swrp`, each concretized abstract precondition separated from `P`
entails the concrete precondition. -/
theorem swrp_transport (h : P ⊢ swrp γ c a Q) (Qa : β → A) :
    P ∗ γ (a Qa) ⊢ WPMonadBI.wp c (swrpPost γ Q Qa) :=
  wand_elim (h.trans (forall_elim Qa))

/-- Transport to a triple of the concrete program. -/
theorem swrp_transport_triple (h : P ⊢ swrp γ c a Q) {P' : Ω} {Qa : β → A}
    (hpre : P' ⊢ γ (a Qa)) : TripleBI iprop(P ∗ P') c (swrpPost γ Q Qa) :=
  (sep_mono_right hpre).trans (swrp_transport h Qa)

/-- Consequence in the return relation. -/
theorem swrp_mono (hQ : ∀ v w, Q v w ⊢ Q' v w) : swrp γ c a Q ⊢ swrp γ c a Q' :=
  swrp_intro fun Qa => (swrp_transport .rfl Qa).trans
    (WPMonadBI.wp_mono c fun v => exists_mono fun w => sep_mono_left (hQ v w))

/-- Consequence in the abstract transformer, seen through `γ`. -/
theorem swrp_mono_abstract {a' : (β → A) → A} (ha : ∀ Qa, γ (a' Qa) ⊢ γ (a Qa)) :
    swrp γ c a Q ⊢ swrp γ c a' Q :=
  swrp_intro fun Qa => (sep_mono_right (ha Qa)).trans (swrp_transport .rfl Qa)

/-- The return of related values refines the return. -/
theorem swrp_pure (v : α) (w : β) :
    Q v w ⊢ swrp γ (Pure.pure v : M α) (fun Qa => Qa w) Q :=
  swrp_intro fun Qa =>
    (exists_intro (Ψ := fun w => iprop(Q v w ∗ γ (Qa w))) w).trans
      (WPMonadBI.wp_pure v (swrpPost γ Q Qa))

/-- Sequencing: a refinement whose return relation is the refinement of the continuations
refines the sequence, when the abstract sequence `ab` is below the composite of `a` and `g`
seen through `γ`. -/
theorem swrp_bind {f : α → M α'} {g : β → (β' → A) → A} {ab : (β' → A) → A}
    {R : α' → β' → Ω} (hab : ∀ Qb, γ (ab Qb) ⊢ γ (a fun w => g w Qb)) :
    swrp γ c a (fun v w => swrp γ (f v) (g w) R) ⊢ swrp γ (c >>= f) ab R :=
  swrp_intro fun Qb => (sep_mono_right (hab Qb)).trans <| (swrp_transport .rfl _).trans <|
    (WPMonadBI.wp_mono c fun _ => exists_elim fun _ => swrp_transport .rfl Qb).trans
      (WPMonadBI.wp_bind c f _)

/-- Sequencing with an intermediate return relation. -/
theorem swrp_bind_rule {f : α → M α'} {g : β → (β' → A) → A} {ab : (β' → A) → A}
    {R : α' → β' → Ω} (hab : ∀ Qb, γ (ab Qb) ⊢ γ (a fun w => g w Qb))
    (hc : P ⊢ swrp γ c a Q) (hf : ∀ v w, Q v w ⊢ swrp γ (f v) (g w) R) :
    P ⊢ swrp γ (c >>= f) ab R :=
  hc.trans ((swrp_mono hf).trans (swrp_bind hab))

/-- Frame: a resource separated from a refinement is separated from its return relation. -/
theorem swrp_frame [WPFrameBI M Ω] (F : Ω) :
    swrp γ c a Q ∗ F ⊢ swrp γ c a (fun v w => iprop(Q v w ∗ F)) :=
  swrp_intro fun Qa => sep_right_comm.1.trans <|
    (sep_mono_left (swrp_transport .rfl Qa)).trans <| (WPFrameBI.wp_frame c _ F).trans <|
      WPMonadBI.wp_mono c fun _ =>
        sep_exists_right.1.trans (exists_mono fun _ => sep_right_comm.1)

/-- Frame in the concretization: a refinement along `γ` is one along `γ` separated from any
resource. -/
theorem swrp_frame_conc [WPFrameBI M Ω] (F : Ω) :
    swrp γ c a Q ⊢ swrp (fun x => iprop(γ x ∗ F)) c a Q :=
  swrp_intro fun Qa => sep_assoc.2.trans <|
    (sep_mono_left (swrp_transport .rfl Qa)).trans <| (WPFrameBI.wp_frame c _ F).trans <|
      WPMonadBI.wp_mono c fun _ => sep_exists_right.1.trans (exists_mono fun _ => sep_assoc.1)

section Pasting

variable {N : Type u' → Type v'} {B : Type w''} [Iris.BI B] [Monad N] [WPMonadBI N B]
  {δ : Type u''}

/-- The composite return relation through the outer concretization `γ₂`. -/
def swrpRelComp (γ₂ : B → Ω) (Q₂ : α → β → Ω) (Q₁ : β → δ → B) : α → δ → Ω :=
  fun v z => iprop(∃ w, Q₂ v w ∗ γ₂ (Q₁ w z))

/-- Vertical pasting. The outer concretization is monotone, preserves the suprema over the
abstract return values, is lax monoidal at the inner precondition and oplax monoidal at the
inner return relation. -/
theorem swrp_vcomp {γ₂ : B → Ω} {γ₁ : A → B} {b : N β} {a : (δ → A) → A} {P₁ : B}
    {P₂ : Ω} {Q₂ : α → β → Ω} {Q₁ : β → δ → B}
    (hmono : ∀ {X Y : B}, (X ⊢ Y) → γ₂ X ⊢ γ₂ Y)
    (hsup : ∀ f : δ → B, γ₂ iprop(∃ z, f z) ⊢ ∃ z, γ₂ (f z))
    (hlax : ∀ x, γ₂ P₁ ∗ γ₂ (γ₁ x) ⊢ γ₂ iprop(P₁ ∗ γ₁ x))
    (hoplax : ∀ w z x, γ₂ iprop(Q₁ w z ∗ γ₁ x) ⊢ γ₂ (Q₁ w z) ∗ γ₂ (γ₁ x))
    (h₁ : P₁ ⊢ swrp γ₁ b a Q₁) (h₂ : P₂ ⊢ swrp γ₂ c (WPMonadBI.wp b) Q₂) :
    P₂ ∗ γ₂ P₁ ⊢ swrp (fun x => γ₂ (γ₁ x)) c a (swrpRelComp γ₂ Q₂ Q₁) :=
  swrp_intro fun Qa => sep_assoc.1.trans <|
    (sep_mono_right ((hlax _).trans (hmono (swrp_transport h₁ Qa)))).trans <|
      (swrp_transport h₂ _).trans <| WPMonadBI.wp_mono c fun v => exists_elim fun w =>
        (sep_mono_right ((hsup _).trans (exists_mono fun z => hoplax w z (Qa z)))).trans <|
          sep_exists_left.1.trans <| exists_mono fun z => sep_assoc.2.trans <|
            sep_mono_left (exists_intro (Ψ := fun w => iprop(Q₂ v w ∗ γ₂ (Q₁ w z))) w)

end Pasting

end Generic

/-! ## Rules with the unit and embedded propositions -/

section Unit

variable {M : Type u → Type v} {Ω : Type w} [Iris.BI Ω] [Monad M] [WPMonadBI M Ω]
  {α : Type u} {A : Type w'} {β : Type u'}
  {γ : A → Ω} {c : M α} {a : (β → A) → A} {Q : α → β → Ω}

/-- Closed refinement is the lax square of `γ`, `a` and the weakest precondition of `c`. -/
theorem emp_entails_swrp_iff :
    (emp ⊢ swrp γ c a Q) ↔ ∀ Qa, γ (a Qa) ⊢ WPMonadBI.wp c (swrpPost γ Q Qa) :=
  ⟨fun h Qa => emp_sep.2.trans (swrp_transport h Qa),
    fun h => swrp_intro fun Qa => emp_sep.1.trans (h Qa)⟩

/-- Reflexivity at the identity concretization and the relation of equality. -/
theorem swrp_refl :
    emp ⊢ swrp (fun X : Ω => X) c (WPMonadBI.wp c) (fun v v' => iprop(<affine> ⌜v = v'⌝)) := by
  refine emp_entails_swrp_iff.2 fun Qa => WPMonadBI.wp_mono c fun v => ?_
  unfold swrpPost
  iintro H
  iexists v
  iframe H
  ipureintro
  rfl

/-- Vertical pasting of closed refinements with a heap-independent inner return relation: the
outer concretization need only be monotone and preserve suprema. -/
theorem swrp_vcomp_pure {N : Type u' → Type v'} {B : Type w''} [Iris.BI B] [Monad N]
    [WPMonadBI N B] {δ : Type u''} {γ₂ : B → Ω} {γ₁ : A → B} {b : N β} {a : (δ → A) → A}
    {P : Ω} {r : β → δ → Prop}
    (hmono : ∀ {X Y : B}, (X ⊢ Y) → γ₂ X ⊢ γ₂ Y)
    (hsup : ∀ {ι : Type u''} (f : ι → B), γ₂ iprop(∃ i, f i) ⊢ ∃ i, γ₂ (f i))
    (h₁ : emp ⊢ swrp γ₁ b a (fun w z => iprop(<affine> ⌜r w z⌝)))
    (h₂ : P ⊢ swrp γ₂ c (WPMonadBI.wp b) Q) :
    P ⊢ swrp (fun x => γ₂ (γ₁ x)) c a
      (fun v z => iprop(∃ w, Q v w ∗ <affine> ⌜r w z⌝)) := by
  refine swrp_intro fun Qa => (sep_mono_right (hmono (emp_entails_swrp_iff.1 h₁ Qa))).trans <|
    (swrp_transport h₂ _).trans <| WPMonadBI.wp_mono c fun v => exists_elim fun w => ?_
  have hin : swrpPost γ₁ (fun w z => iprop(<affine> ⌜r w z⌝)) Qa w ⊢
      ∃ s : {z // r w z}, γ₁ (Qa s.1) := by
    unfold swrpPost
    iintro ⟨%z, %hz, H⟩
    iexists ⟨z, hz⟩
    iexact H
  refine (sep_mono_right ((hmono hin).trans (hsup _))).trans ?_
  unfold swrpPost
  iintro ⟨HQ, %s, H⟩
  iexists s.1
  iframe H
  iexists w
  iframe HQ
  ipureintro
  exact s.2

/-- Where `∗` is `∧`, `swrp` is the cartesian residual, the formula of `RefinementWP.wrp`. -/
theorem swrp_biEntails_of_sep_and (hsep : ∀ X Y : Ω, X ∗ Y ⊣⊢ X ∧ Y) :
    swrp γ c a Q ⊣⊢
      ∀ Qa, γ (a Qa) → WPMonadBI.wp c (fun v => iprop(∃ w, Q v w ∧ γ (Qa w))) := by
  constructor
  · exact forall_intro fun Qa => imp_intro <| (hsep _ _).2.trans <|
      (swrp_transport .rfl Qa).trans <|
        WPMonadBI.wp_mono c fun _ => exists_mono fun _ => (hsep _ _).1
  · refine swrp_intro fun Qa => (hsep _ _).1.trans ((imp_elim ?_).trans
      (WPMonadBI.wp_mono c fun _ => exists_mono fun _ => (hsep _ _).2))
    exact forall_elim Qa

/-- The step-indexed propositions are a BI whose `∗` is `∧`. -/
example {M : Type u → Type v} [Monad M] [WPMonadBI M Iris.SiProp] (γ : A → Iris.SiProp)
    (c : M α) (a : (β → A) → A) (Q : α → β → Iris.SiProp) :
    swrp γ c a Q ⊣⊢
      ∀ Qa, γ (a Qa) → WPMonadBI.wp c (fun v => iprop(∃ w, Q v w ∧ γ (Qa w))) :=
  swrp_biEntails_of_sep_and fun _ _ => ⟨.rfl, .rfl⟩

end Unit

/-! ## The instance at `HProp` and `slWP` -/

section Heap

open CatCrypt.Core
open scoped Std.WP
open RefinementWP (Concretization MonoPT optD Refines)

/-- An existential of heap propositions holds at a state when one of its members does. -/
theorem hProp_exists_iff {ι : Sort u} {f : ι → HProp} {σ : IState} :
    (iprop(∃ i, f i) : HProp) σ ↔ ∃ i, f i σ :=
  ⟨fun ⟨_, ⟨i, rfl⟩, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨f i, ⟨i, rfl⟩, h⟩⟩

/-- The concretization of a relation of heap states preserves the suprema of the BI. -/
theorem ofStateRel_exists (SR : IState → IState → Prop) {ι : Sort u} (f : ι → HProp) :
    (Concretization.ofStateRel SR).pred iprop(∃ i, f i) ⊢
      ∃ i, (Concretization.ofStateRel SR).pred (f i) := by
  rintro σ ⟨τ, hτ, hf⟩
  obtain ⟨i, hi⟩ := hProp_exists_iff.1 hf
  exact hProp_exists_iff.2 ⟨i, τ, hτ, hi⟩

/-- The concretization of a renaming `e` of locations. -/
def reindexConc (e : Nat ≃ Nat) : Concretization HProp HProp :=
  Concretization.ofStateRel fun σ τ => τ = σ ∘ e

/-- A renaming of locations is lax monoidal. -/
theorem reindexConc_sep_le (e : Nat ≃ Nat) (P Q : HProp) :
    (reindexConc e).pred P ∗ (reindexConc e).pred Q ⊢ (reindexConc e).pred iprop(P ∗ Q) := by
  rintro σ ⟨σ₁, σ₂, rfl, hd, ⟨_, rfl, hP⟩, ⟨_, rfl, hQ⟩⟩
  refine ⟨_, rfl, σ₁ ∘ e, σ₂ ∘ e, ?_, fun i => hd (e i), hP, hQ⟩
  funext i
  simp [HeapAlgebra.istate_union_apply]

/-- A renaming of locations is oplax monoidal. -/
theorem reindexConc_le_sep (e : Nat ≃ Nat) (P Q : HProp) :
    (reindexConc e).pred iprop(P ∗ Q) ⊢ (reindexConc e).pred P ∗ (reindexConc e).pred Q := by
  rintro σ ⟨_, rfl, τ₁, τ₂, hu, hd, hP, hQ⟩
  refine ⟨τ₁ ∘ e.symm, τ₂ ∘ e.symm, ?_, fun i => hd (e.symm i),
    ⟨τ₁, ?_, hP⟩, ⟨τ₂, ?_, hQ⟩⟩
  · funext i
    simpa [HeapAlgebra.istate_union_apply] using congrFun hu (e.symm i)
  · simp [Function.comp_assoc]
  · simp [Function.comp_assoc]

/-- Vertical pasting along a renaming of locations, which satisfies the four hypotheses of
`swrp_vcomp`. -/
theorem swrp_vcomp_reindex {N : Type u' → Type v'} [Monad N] [WPMonadBI N HProp] {α : Type u}
    {β : Type u'} {δ : Type u''} {A : Type w'} (e : Nat ≃ Nat) {γ₁ : A → HProp}
    {c : SPComp α} {b : N β} {a : (δ → A) → A} {P₁ P₂ : HProp} {Q₂ : α → β → HProp}
    {Q₁ : β → δ → HProp} (h₁ : P₁ ⊢ swrp γ₁ b a Q₁)
    (h₂ : P₂ ⊢ swrp (reindexConc e).pred c (WPMonadBI.wp b) Q₂) :
    P₂ ∗ (reindexConc e).pred P₁ ⊢
      swrp (fun x => (reindexConc e).pred (γ₁ x)) c a
        (swrpRelComp (reindexConc e).pred Q₂ Q₁) :=
  swrp_vcomp (reindexConc e).pred_mono (ofStateRel_exists _)
    (fun _ => reindexConc_sep_le e _ _) (fun _ _ _ => reindexConc_le_sep e _ _) h₁ h₂

/-- Every state relation satisfies the two hypotheses of `swrp_vcomp_pure`. -/
example {α β δ A : Type} (SR : IState → IState → Prop) {γ₁ : A → HProp} {c : SPComp α}
    {b : SPComp β} {a : (δ → A) → A} {P : HProp} {Q : α → β → HProp} {r : β → δ → Prop}
    (h₁ : emp ⊢ swrp γ₁ b a (fun w z => iprop(<affine> ⌜r w z⌝)))
    (h₂ : P ⊢ swrp (Concretization.ofStateRel SR).pred c (WPMonadBI.wp b) Q) :
    P ⊢ swrp (fun x => (Concretization.ofStateRel SR).pred (γ₁ x)) c a
      (fun v z => iprop(∃ w, Q v w ∗ <affine> ⌜r w z⌝)) :=
  swrp_vcomp_pure (Concretization.ofStateRel SR).pred_mono (ofStateRel_exists SR) h₁ h₂

/-! ### Relation to `RefinementWP.wrp` -/

section WRP

variable {α β : Type} {APred AProg : Type} [Std.WP.Assertion APred]
  [Std.WP.WP AProg β APred Unit] {γ : Concretization HProp APred} {eps : Unit → Unit}
  {c : SPComp α} {a : AProg} {r : α → β → Prop}

/-- The weakest precondition `slWP c` as a monotone predicate transformer, the form in which
`RefinementWP.wrp` takes a concrete program. -/
def slPT (c : SPComp α) : MonoPT IState α where
  trans := slWP c
  mono _ _ h := slWP_mono h

/-- At a heap-independent return relation the separating postcondition is the postcondition
of `RefinementWP.wrp`. -/
theorem swrpPost_affine_eq_post (γ : Concretization HProp APred) (r : α → β → Prop)
    (Qa : β → APred) :
    swrpPost γ.pred (fun v w => iprop(<affine> ⌜r v w⌝)) Qa =
      γ.post (fun v w _ => r v w) Qa := by
  funext v σ
  refine propext (hProp_exists_iff.trans
    (Iff.trans (exists_congr fun w => ?_) (Concretization.post_apply γ _ Qa v σ).symm))
  constructor
  · rintro ⟨σ₁, σ₂, rfl, -, ⟨rfl, hr⟩, hγ⟩
    exact ⟨hr, by rwa [← Iris.Instances.Data.empty_union]⟩
  · rintro ⟨hr, hγ⟩
    exact ⟨∅, σ, Iris.Instances.Data.empty_union, Iris.Instances.Data.empty_disjoint,
      ⟨rfl, hr⟩, hγ⟩

/-- **Closed separating refinement is refinement.** At a heap-independent return relation,
`emp ⊢ swrp` is `RefinementWP.Refines` at `top`, for every concretization. -/
theorem emp_entails_swrp_iff_refines :
    (emp ⊢ swrp γ.pred c (fun Qa => Std.WP.WP.wp a Qa ())
        (fun v w => iprop(<affine> ⌜r v w⌝))) ↔
      Refines Lean.Order.top γ eps (slPT c) a (fun v w _ => r v w) := by
  rw [emp_entails_swrp_iff, RefinementWP.refines_top_iff]
  simp only [swrpPost_affine_eq_post]
  exact ⟨fun h Qa _ => h Qa, fun h Qa => h Qa ()⟩

/-- Separating refinement gives refinement when the meet of the precondition and each
concretized abstract assertion splits. -/
private theorem refines_of_and_entails_sep {P : HProp}
    (hsep : ∀ x, P ∧ γ.pred x ⊢ P ∗ γ.pred x)
    (h : P ⊢ swrp γ.pred c (fun Qa => Std.WP.WP.wp a Qa ())
      (fun v w => iprop(<affine> ⌜r v w⌝))) :
    Refines P γ eps (slPT c) a (fun v w _ => r v w) := by
  refine RefinementWP.wrp_intro fun Qa Ea σ hσ => ?_
  rw [Lean.Order.meet_apply, Lean.Order.meet_prop_eq_and] at hσ
  rw [← swrpPost_affine_eq_post]
  exact swrp_transport h Qa σ (hsep _ σ hσ)

/-- Under a persistent precondition, separating refinement gives refinement. -/
theorem refines_of_entails_swrp {P : HProp} [Persistent P]
    (h : P ⊢ swrp γ.pred c (fun Qa => Std.WP.WP.wp a Qa ())
      (fun v w => iprop(<affine> ⌜r v w⌝))) :
    Refines P γ eps (slPT c) a (fun v w _ => r v w) :=
  refines_of_and_entails_sep (fun _ => persistent_and_sep_mp) h

/-- At a persistent concretization, `swrp` entails `RefinementWP.wrp`. -/
theorem swrp_entails_wrp [∀ x, Persistent (γ.pred x)] :
    swrp γ.pred c (fun Qa => Std.WP.WP.wp a Qa ()) (fun v w => iprop(<affine> ⌜r v w⌝)) ⊢
      RefinementWP.wrp γ eps (slPT c) a (fun v w _ => r v w) :=
  refines_of_and_entails_sep (fun _ => persistent_and_sep_mp) .rfl

/-- The concretization of a relation that does not read the heap is persistent, so there
`swrp` entails `RefinementWP.wrp`. -/
example {X : Type} (p : X → Prop) (a : MonoPT X β) :
    swrp (Concretization.ofStateRel fun (_ : IState) y => p y).pred c a.trans
        (fun v w => iprop(<affine> ⌜r v w⌝)) ⊢
      RefinementWP.wrp (Concretization.ofStateRel fun (_ : IState) y => p y) eps (slPT c) a
        (fun v w _ => r v w) :=
  have : ∀ x, Persistent ((Concretization.ofStateRel fun (_ : IState) y => p y).pred x) :=
    fun _ => ⟨fun _ h => h⟩
  swrp_entails_wrp (γ := Concretization.ofStateRel fun (_ : IState) y => p y) (a := a)

end WRP

/-! ### A write framed past another location -/

/-- The abstract state is the value of the location `ℓ`. -/
def cellConc (ℓ : Location) : Concretization HProp (ℓ.ty → Prop) :=
  Concretization.ofStateRel fun σ x => (ℓ ↦ₜ x) σ

/-- A write to `ℓ` refines the assignment of the abstract value. -/
theorem swrp_set (ℓ : Location) (x : ℓ.ty) :
    emp ⊢ swrp (cellConc ℓ).pred (SPComp.set ℓ x)
      (optD fun _ : ℓ.ty => some ((), x)).trans (fun _ _ => iprop(emp)) := by
  refine emp_entails_swrp_iff.2 fun Qa => ?_
  rintro σ ⟨y, hy, hQa⟩
  refine slWP_mono (fun _ σ' hσ' => ?_) σ (slWP_set ℓ x σ (ptsTo_ptsToAny ℓ y σ hy))
  exact hProp_exists_iff.2 ⟨(), ∅, σ', Iris.Instances.Data.empty_union,
    Iris.Instances.Data.empty_disjoint, rfl, x, hσ', hQa⟩

/-- **Frame.** The refinement of a write to `ℓ₁` carries the points-to of `ℓ₂`, which neither
the concretization nor the abstract state mentions. -/
theorem swrp_set_framed (ℓ₁ ℓ₂ : Location) (x : ℓ₁.ty) (y : ℓ₂.ty) :
    (ℓ₂ ↦ₜ y) ⊢ swrp (cellConc ℓ₁).pred (SPComp.set ℓ₁ x)
      (optD fun _ : ℓ₁.ty => some ((), x)).trans (fun _ _ => ℓ₂ ↦ₜ y) :=
  emp_sep.2.trans <| (sep_mono_left (swrp_set ℓ₁ x)).trans <|
    (swrp_frame _).trans (swrp_mono fun _ _ => emp_sep.1)

/-- The write refines the assignment in the sense of `RefinementWP.Refines`. -/
example (ℓ : Location) (x : ℓ.ty) :
    Refines Lean.Order.top (cellConc ℓ) id (slPT (SPComp.set ℓ x))
      (optD fun _ : ℓ.ty => some ((), x)) (fun _ _ _ => True) :=
  emp_entails_swrp_iff_refines.1 <|
    (swrp_set ℓ x).trans (swrp_mono fun _ _ _ hσ => ⟨hσ, trivial⟩)

/-- Two writes in sequence carry the untouched location by the frame and bind rules. -/
example (ℓ₁ ℓ₂ : Location) (x x' : ℓ₁.ty) (y : ℓ₂.ty) :
    (ℓ₂ ↦ₜ y) ⊢ swrp (cellConc ℓ₁).pred (SPComp.set ℓ₁ x >>= fun _ => SPComp.set ℓ₁ x')
      (optD (fun _ : ℓ₁.ty => some ((), x)) >>= fun _ =>
        optD fun _ : ℓ₁.ty => some ((), x')).trans
      (fun _ _ => ℓ₂ ↦ₜ y) :=
  swrp_bind_rule (g := fun _ => (optD fun _ : ℓ₁.ty => some ((), x')).trans) (fun _ => .rfl)
    (swrp_set_framed ℓ₁ ℓ₂ x y) fun _ _ => swrp_set_framed ℓ₁ ℓ₂ x' y

/-- Transport of the framed refinement gives the triple in which `ℓ₂` is preserved. -/
example (ℓ₁ ℓ₂ : Location) (x₀ x : ℓ₁.ty) (y : ℓ₂.ty) :
    TripleBI (M := SPComp) iprop((ℓ₂ ↦ₜ y) ∗ (ℓ₁ ↦ₜ x₀)) (SPComp.set ℓ₁ x)
      (fun _ => iprop((ℓ₂ ↦ₜ y) ∗ (ℓ₁ ↦ₜ x))) :=
  (swrp_transport_triple (swrp_set_framed ℓ₁ ℓ₂ x y) (Qa := fun _ z => z = x)
      fun _ h => ⟨x₀, h, rfl⟩).conseq .rfl
    fun _ => exists_elim fun _ => sep_mono_right fun _ ⟨_, hz, e⟩ => e ▸ hz

end Heap

end CatCrypt.Crypto.IrisBridge
