/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Iris.ProofMode
public import CatCryptCore.Crypto.Bridges.IrisBridge.SLWP

/-!
# A BI-parametric weakest-precondition and verification-condition calculus

This file defines a weakest-precondition calculus that is parametric in an
arbitrary complete `Iris.BI` `Ω`, and instantiates it at `Ω := HProp`
(iris-lean's Classical heap BI) so that verification conditions are
entailments of the BI, with `∗` and ownership, discharged in the Iris proof
mode.

`PredTransBI` is the continuation predicate transformer valued in `Ω`.
`WPMonadBI` is a wp with `pure`, `bind` and monotonicity laws that hold over
any BI. `TripleBI` is the Hoare triple `P ⊢ wp c Q`; its compositional lemmas
(`pure`, `bind`, `conseq`, `frame`) reduce a triple to sub-triples and to
entailments in `Ω`. The frame rule carries an untouched resource `R` across a
command, and the remaining verification condition is an entailment about
`∗`-split ownership, proved with `iintro` and `iframe`.

The instance at `HProp` is built from the frame-quantified support-level wp
`slWP`, which is flat (no step-indexing) and of partial correctness. It
exposes the laws that hold only one way as entailments:

* `wp_pure` is the introduction direction `Q a ⊢ wp (pure a) Q`
  (`slWP_pure_intro`); the reverse needs `Realizable` (`slWP_pure_elim`).
* `wp_bind` is the sequencing direction
  `wp m (fun a => wp (f a) Q) ⊢ wp (m >>= f) Q` (`slWP_bind`).

The frame law `slWP_frame` is packaged as the separate mixin `WPFrameBI`.
At `Ω := HProp`, `TripleBI P c Q` is definitionally `P ⊢ slWP c Q`
(`tripleBI_eq`).
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.IrisBridge

open CatCrypt.Core
open Iris.BI
open HeapAlgebra

universe u v w

/-! ## The continuation predicate transformer valued in a BI -/

/-- The continuation predicate transformer valued in a BI `Ω`: a map from
`Ω`-valued postconditions on `α` to an `Ω`-valued precondition. This is the
carrier the wp of a computation produces. -/
def PredTransBI (Ω : Type w) [Iris.BI Ω] (α : Type u) : Type (max u w) :=
  (α → Ω) → Ω

namespace PredTransBI

variable {Ω : Type w} [Iris.BI Ω]

/-- Monotonicity of a transformer: weakening the postcondition weakens the
precondition. The wp laws all package a proof of this. -/
def Mono {α : Type u} (t : PredTransBI Ω α) : Prop :=
  ∀ Q Q' : α → Ω, (∀ a, Q a ⊢ Q' a) → t Q ⊢ t Q'

/-- Unit of the continuation transformer: evaluate the postcondition at `a`. -/
def pureT {α : Type u} (a : α) : PredTransBI Ω α := fun Q => Q a

/-- Kleisli composition of continuation transformers. -/
def bindT {α : Type u} {β : Type u} (t : PredTransBI Ω α)
    (k : α → PredTransBI Ω β) : PredTransBI Ω β :=
  fun Q => t (fun a => k a Q)

/-- Left identity (continuation monad, definitional). -/
theorem bindT_pureT {α β : Type u} (a : α) (k : α → PredTransBI Ω β) :
    bindT (pureT a) k = k a := rfl

/-- Right identity (continuation monad, definitional). -/
theorem bindT_pureT_right {α : Type u} (t : PredTransBI Ω α) :
    bindT t pureT = t := rfl

/-- Associativity (continuation monad, definitional). -/
theorem bindT_assoc {α β γ : Type u} (t : PredTransBI Ω α)
    (k : α → PredTransBI Ω β) (l : β → PredTransBI Ω γ) :
    bindT (bindT t k) l = bindT t (fun a => bindT (k a) l) := rfl

/-- `pureT a` is monotone. -/
theorem pureT_mono {α : Type u} (a : α) : Mono (pureT (Ω := Ω) a) :=
  fun _ _ h => h a

/-- `bindT` preserves monotonicity. -/
theorem bindT_mono {α β : Type u} {t : PredTransBI Ω α}
    {k : α → PredTransBI Ω β} (ht : Mono t) (hk : ∀ a, Mono (k a)) :
    Mono (bindT t k) :=
  fun _ _ h => ht _ _ (fun a => hk a _ _ h)

end PredTransBI

/-! ## The BI-generic weakest-precondition interface -/

/-- A BI-generic weakest-precondition calculus for a monad `M` valued in a BI
`Ω`. `wp c` is the continuation predicate transformer of `c`; the three laws
are the `pure`/`bind`/monotonicity structure any such wp must satisfy, stated
in the directions that hold over an arbitrary BI. `wp_pure`/`wp_bind` are
entailments (not bi-entailments): that is all the `TripleBI` VC generator
consumes, and it is exactly what the flat `SLWP` instance provides. -/
class WPMonadBI (M : Type u → Type v) (Ω : Type w) [Iris.BI Ω] [Monad M] where
  /-- The weakest-precondition transformer of a computation. -/
  wp {α : Type u} : M α → PredTransBI Ω α
  /-- `pure` introduction: the postcondition at `a` entails the wp of `pure a`. -/
  wp_pure {α : Type u} (a : α) (Q : α → Ω) : Q a ⊢ wp (pure a) Q
  /-- Sequencing (lax): the wp of the bind is entailed by the nested wp. -/
  wp_bind {α β : Type u} (m : M α) (f : α → M β) (Q : β → Ω) :
    wp m (fun a => wp (f a) Q) ⊢ wp (m >>= f) Q
  /-- Monotonicity: weaken the postcondition inside the wp. -/
  wp_mono {α : Type u} (m : M α) {Q Q' : α → Ω} (h : ∀ a, Q a ⊢ Q' a) :
    wp m Q ⊢ wp m Q'

/-- The frame rule as a mixin over `WPMonadBI`: a resource `R` separated from
the wp threads through the command untouched. Kept separate because it is not
derivable from `pure`/`bind`/`mono` alone; the `SLWP` instance supplies it
unconditionally (`slWP_frame`). -/
class WPFrameBI (M : Type u → Type v) (Ω : Type w) [Iris.BI Ω] [Monad M]
    [WPMonadBI M Ω] where
  /-- Frame: `wp c Q ∗ R ⊢ wp c (fun a => Q a ∗ R)`. -/
  wp_frame {α : Type u} (c : M α) (Q : α → Ω) (R : Ω) :
    WPMonadBI.wp c Q ∗ R ⊢ WPMonadBI.wp c (fun a => iprop(Q a ∗ R))

/-! ## The Hoare-triple / VC layer -/

/-- A BI-generic Hoare triple: the precondition entails the wp of the command
at the postcondition. Its compositional lemmas below are the VC generator —
each reduces a triple to sub-VCs that are entailments in `Ω`. -/
def TripleBI {M : Type u → Type v} {Ω : Type w} [Iris.BI Ω] [Monad M]
    [WPMonadBI M Ω] {α : Type u} (P : Ω) (c : M α) (Q : α → Ω) : Prop :=
  P ⊢ WPMonadBI.wp c Q

namespace TripleBI

variable {M : Type u → Type v} {Ω : Type w} [Iris.BI Ω] [Monad M]
  [WPMonadBI M Ω]

/-- VC for `pure`: the triple `{P} pure a {Q}` reduces to the entailment
`P ⊢ Q a`. -/
theorem pure {α : Type u} {P : Ω} {a : α} {Q : α → Ω} (h : P ⊢ Q a) :
    TripleBI P (Pure.pure a : M α) Q :=
  h.trans (WPMonadBI.wp_pure a Q)

/-- VC for `bind`: a triple for `c >>= f` reduces to a triple for `c` with an
intermediate postcondition `Q'` and, for each result `a`, a triple for `f a`. -/
theorem bind {α β : Type u} {P : Ω} {c : M α} {f : α → M β} {Q' : α → Ω}
    {Q : β → Ω} (hc : TripleBI P c Q') (hf : ∀ a, TripleBI (Q' a) (f a) Q) :
    TripleBI P (c >>= f) Q :=
  (hc.trans (WPMonadBI.wp_mono c hf)).trans (WPMonadBI.wp_bind c f Q)

/-- Rule of consequence: strengthen the precondition and weaken the
postcondition. The two side conditions are entailment VCs in `Ω`. -/
theorem conseq {α : Type u} {P P' : Ω} {c : M α} {Q Q' : α → Ω}
    (hP : P' ⊢ P) (ht : TripleBI P c Q) (hQ : ∀ a, Q a ⊢ Q' a) :
    TripleBI P' c Q' :=
  (hP.trans ht).trans (WPMonadBI.wp_mono c hQ)

/-- The frame rule at the triple layer (needs `WPFrameBI`): a separated
resource `R` is carried across `c`, with `∗` in both pre- and postcondition. -/
theorem frame {α : Type u} [WPFrameBI M Ω] {P : Ω} {c : M α} {Q : α → Ω}
    (R : Ω) (ht : TripleBI P c Q) :
    TripleBI iprop(P ∗ R) c (fun a => iprop(Q a ∗ R)) :=
  (sep_mono ht .rfl).trans (WPFrameBI.wp_frame c Q R)

end TripleBI

/-! ## The `Ω := HProp` instance

`HProp` is iris-lean's Classical heap BI. The wp is the frame-quantified
support-level wp `slWP`; the three interface laws are its
structural laws `slWP_pure_intro`, `slWP_bind`, `slWP_mono`, and the frame
mixin is `slWP_frame`. `SPComp`'s monad `pure`/`>>=` are definitionally
`SPComp.pure`/`SPComp.bind` (`SPComp.monad_pure_eq`/`monad_bind_eq`). -/

/-- The flat separation-logic instance: `wp := slWP`. -/
noncomputable instance instWPMonadBISPComp : WPMonadBI SPComp HProp where
  wp c := fun Q => slWP c Q
  wp_pure := by intro α a Q; exact slWP_pure_intro a Q
  wp_bind := by intro α β m f Q; exact slWP_bind m f Q
  wp_mono := by intro α m Q Q' h; exact slWP_mono h

/-- The frame mixin at `HProp`: the unconditional frame rule `slWP_frame`. -/
noncomputable instance instWPFrameBISPComp : WPFrameBI SPComp HProp where
  wp_frame := by intro α c Q R; exact slWP_frame c Q R

/-- `wp` at the `HProp` instance is definitionally `slWP`. -/
theorem wp_eq_slWP {α : Type u} (c : SPComp α) (Q : α → HProp) :
    WPMonadBI.wp c Q = slWP c Q := rfl

/-- `TripleBI` at the `HProp` instance is definitionally `P ⊢ slWP c Q`. -/
theorem tripleBI_eq {α : Type u} (P : HProp) (c : SPComp α) (Q : α → HProp) :
    TripleBI P c Q = (P ⊢ slWP c Q) := rfl

/-! ## A separating verification condition discharged in the proof mode

A triple about a `SPComp` heap write whose pre- and postcondition are `∗`-split
ownership of two distinct locations. It is assembled entirely from the
`TripleBI.*` VC lemmas (`slWP_set` as the primitive triple, then `frame` to
ship the untouched second location, then `conseq` to reorder the ownership),
and the two residual VCs are **separating** `iProp` entailments discharged in
the Iris proof mode with `iintro`/`iframe`. No preservation obligation about
the program is discharged: the frame rule absorbs it. -/
example (ℓ₁ ℓ₂ : Location) (v₁ : ℓ₁.ty) (v₂ : ℓ₂.ty) (w : ℓ₁.ty) :
    TripleBI (M := SPComp) iprop((ℓ₂ ↦ₜ v₂) ∗ (ℓ₁ ↦ₜ v₁))
      (SPComp.set ℓ₁ w)
      (fun _ => iprop((ℓ₂ ↦ₜ v₂) ∗ (ℓ₁ ↦ₜ w))) := by
  -- Primitive triple for the write: owning `ℓ₁` at any value suffices.
  have base : TripleBI (M := SPComp) (ptsToAny ℓ₁) (SPComp.set ℓ₁ w)
      (fun _ => (ℓ₁ ↦ₜ w : HProp)) := slWP_set ℓ₁ w
  -- Weaken the precondition to concrete ownership `ℓ₁ ↦ₜ v₁`.
  have t0 : TripleBI (M := SPComp) (ℓ₁ ↦ₜ v₁ : HProp) (SPComp.set ℓ₁ w)
      (fun _ => (ℓ₁ ↦ₜ w : HProp)) :=
    base.conseq (ptsTo_ptsToAny ℓ₁ v₁) (fun _ => .rfl)
  -- Frame the untouched second location across the write.
  have t1 : TripleBI (M := SPComp) iprop((ℓ₁ ↦ₜ v₁) ∗ (ℓ₂ ↦ₜ v₂))
      (SPComp.set ℓ₁ w) (fun _ => iprop((ℓ₁ ↦ₜ w) ∗ (ℓ₂ ↦ₜ v₂))) :=
    t0.frame (ℓ₂ ↦ₜ v₂)
  -- Reorder ownership on both sides — the separating VCs, in the proof mode.
  refine t1.conseq ?_ (fun _ => ?_)
  · -- `(ℓ₂ ↦ₜ v₂) ∗ (ℓ₁ ↦ₜ v₁) ⊢ (ℓ₁ ↦ₜ v₁) ∗ (ℓ₂ ↦ₜ v₂)`
    iintro ⟨H2, H1⟩
    iframe
  · -- `(ℓ₁ ↦ₜ w) ∗ (ℓ₂ ↦ₜ v₂) ⊢ (ℓ₂ ↦ₜ v₂) ∗ (ℓ₁ ↦ₜ w)`
    iintro ⟨H1, H2⟩
    iframe

end CatCrypt.Crypto.IrisBridge
