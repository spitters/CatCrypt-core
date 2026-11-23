/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import RefinementWP.Sep
public import Iris.Instances.Classical

/-!
# The ownership-lifted, framed weakest precondition

For a monad `m` with a weakest precondition `wp` over predicates on total states `S`
(`Std.WP.WPMonad m (S → Prop) E`) and an embedding `own : S → State Val` of total states into
the partial states of iris-lean's classical heap model, the ownership lifting `ownWP own c Φ e`
holds at a partial state `σ` when `wp c` holds at every total state whose image is `σ`, with the
postcondition `Φ` read through `own`. It is monotone and satisfies the lax return and bind laws, so
it is again a weakest precondition monad over heap propositions (`ownWPMonad`).

The framed lifted weakest precondition `ownFWP own c Φ e` is the frame closure `fwp` of the
lifting: it quantifies a frame inside the weakest precondition. At it every program frames every
resource (`ownFWP_frame`), with no hypothesis on the program. At a partial state it holds when, for
every disjoint frame state `σf` satisfying a frame `F`, the weakest precondition holds at every
total state whose image is the union, with the postcondition `Φ a ∗ F` read through `own`
(`ownFWP_apply`).

Whether the result is a partial or a total correctness statement is decided by the underlying
`wp`: the construction preserves it.

## Main definitions

* `SepAssertion (HeapProp Val)`, `SepAssertionUnit (HeapProp Val)`: the separating conjunction,
  wand and unit of iris-lean's classical heap propositions, whose order is entailment
  (`heapProp_le_iff`).
* `ownWP`, `ownWPInst`, `ownWPMonad`: the ownership lifting as a transformer, a `WP`
  interpretation and a `WPMonad` (definitions, not instances).
* `ownFWP`, `ownFramedWPMonad`: the frame closure of the lifting.

## Main results

* `ownWP_monotone`, `le_ownWP_pure`, `ownWP_bind_le`: the laws of the lifting.
* `ownFWP_monotone`, `le_ownFWP_pure`, `ownFWP_bind_le`, `ownFWP_frame`: the laws of the framed
  lifting.
* `ownFWP_apply`: the framed lifting at a partial state.

## References

* H. Yang, P. W. O'Hearn, *A Semantic Basis for Local Reasoning*, FoSSaCS 2002.
* A. Charguéraud, *Separation Logic for Sequential Programs*, ICFP 2020.
* R. Jung et al., *Iris from the ground up*, JFP 2018.

## Search words

ownership, partial state, total state, separation logic, frame rule, frame closure, framed weakest
precondition, heap proposition, lifting a weakest precondition
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.IrisBridge

open Std.WP Lean.Order RefinementWP
open Iris.Instances.Classical Iris.Instances.Data Iris.BI

universe u v w z t

/-! ## Heap propositions as separating assertions -/

section HeapProp

variable {Val : Type t}

/-- The order of heap propositions as an assertion lattice is entailment. -/
theorem heapProp_le_iff {P Q : HeapProp Val} : P ⊑ Q ↔ (P ⊢ Q) :=
  Iff.rfl

/-- The separating conjunction and the magic wand of iris-lean's classical heap propositions. -/
instance heapProp_sepAssertion : SepAssertion (HeapProp Val) where
  sep P Q := iprop(P ∗ Q)
  wand P Q := iprop(P -∗ Q)
  sep_mono h₁ h₂ := heapProp_le_iff.2 (Iris.BI.sep_mono h₁ h₂)
  sep_symm := heapProp_le_iff.2 Iris.BI.sep_symm
  sep_assoc_le := heapProp_le_iff.2 sep_assoc.mp
  le_wand_iff := ⟨fun h => heapProp_le_iff.2 (Iris.BI.wand_elim (heapProp_le_iff.1 h)),
    fun h => heapProp_le_iff.2 (Iris.BI.wand_intro (heapProp_le_iff.1 h))⟩

/-- Unfolding the separating conjunction of `heapProp_sepAssertion`. -/
@[simp] theorem heapProp_sep_eq (P Q : HeapProp Val) : SepAssertion.sep P Q = iprop(P ∗ Q) :=
  rfl

/-- Unfolding the wand of `heapProp_sepAssertion`. -/
@[simp] theorem heapProp_wand_eq (P Q : HeapProp Val) :
    SepAssertion.wand P Q = iprop(P -∗ Q) :=
  rfl

/-- The separating conjunction of heap propositions, with the empty state as unit. -/
instance heapProp_sepAssertionUnit : SepAssertionUnit (HeapProp Val) where
  emp := iprop(emp)
  sep_emp_le {p} := heapProp_le_iff.2 (sep_emp (P := p)).mp
  le_sep_emp {p} := heapProp_le_iff.2 (sep_emp (P := p)).mpr

end HeapProp

/-! ## The ownership lifting -/

section Own

variable {m : Type u → Type v} [Monad m] {S : Type w} {E : Type z} [Assertion E]
  [W : WPMonad m (S → Prop) E] {Val : Type t}

/-- The ownership lifting of a weakest precondition on total states: at a partial state `σ`, the
weakest precondition of `c` holds at every total state `s` with `own s = σ`, for the postcondition
`Φ` read through `own`. -/
def ownWP (own : S → State Val) {α : Type u} (c : m α) (Φ : α → HeapProp Val) (e : E) :
    HeapProp Val :=
  fun σ => ∀ s, own s = σ → wp c (fun a s' => Φ a (own s')) e s

variable (own : S → State Val) {α β : Type u}

/-- The ownership lifting is monotone in the normal and the exception postcondition. -/
theorem ownWP_monotone {c : m α} {Φ Φ' : α → HeapProp Val} {e e' : E}
    (hΦ : ∀ a, Φ a ⊑ Φ' a) (he : e ⊑ e') : ownWP own c Φ e ⊑ ownWP own c Φ' e' :=
  fun _ h s hs => WP.wp_monotone (x := c) (fun a s' => hΦ a (own s')) he s (h s hs)

/-- Return: the postcondition at `x` entails the lifting of `pure x`. -/
theorem le_ownWP_pure (x : α) (Φ : α → HeapProp Val) (e : E) :
    Φ x ⊑ ownWP own (pure x : m α) Φ e := by
  intro σ h s hs
  subst hs
  exact WPMonad.pure_le_wp_pure (m := m) x (fun a s' => Φ a (own s')) e s h

/-- Lax bind: the lifting of `c` at the liftings of the continuations entails the lifting of the
sequence. -/
theorem ownWP_bind_le (c : m α) (f : α → m β) (Φ : β → HeapProp Val) (e : E) :
    ownWP own c (fun a => ownWP own (f a) Φ e) e ⊑ ownWP own (c >>= f) Φ e :=
  fun _ h s hs => WPMonad.bind_le_wp_bind c f (fun a s' => Φ a (own s')) e s
    (WP.wp_monotone_post (x := c) (fun _ s' h' => h' s' rfl) s (h s hs))

/-- The ownership lifting as a weakest precondition interpretation of `m α` over heap
propositions. It is a definition and not an instance, since `m α` has its own interpretation. -/
@[instance_reducible] def ownWPInst (α : Type u) : Std.WP.WP (m α) α (HeapProp Val) E where
  trans c := ⟨ownWP own c⟩
  trans_monotone _ _ _ _ _ he hΦ := ownWP_monotone own hΦ he

/-- The ownership lifting as a weakest precondition monad over heap propositions. -/
@[instance_reducible] def ownWPMonad : WPMonad m (HeapProp Val) E where
  toLawfulMonad := W.toLawfulMonad
  toWP := ownWPInst own
  pure_le_wp_pure x Φ e := le_ownWP_pure own x Φ e
  bind_le_wp_bind c f Φ e := ownWP_bind_le own c f Φ e

/-! ## The framed lifting -/

/-- The framed lifted weakest precondition: the frame closure `fwp` of the ownership lifting. -/
noncomputable def ownFWP (c : m α) (Φ : α → HeapProp Val) (e : E) : HeapProp Val :=
  @fwp (m α) α (HeapProp Val) E _ _ _ (ownWPInst own α) c Φ e

/-- The framed lifting as a weakest precondition monad over heap propositions. -/
@[instance_reducible] noncomputable def ownFramedWPMonad : WPMonad m (HeapProp Val) E :=
  @framedWPMonad m _ (HeapProp Val) E _ _ _ (ownWPMonad own)

/-- The weakest precondition of `ownFramedWPMonad` is `ownFWP`. -/
theorem ownFramedWPMonad_wp (c : m α) (Φ : α → HeapProp Val) (e : E) :
    ((ownFramedWPMonad own).toWP α).wp c Φ e = ownFWP own c Φ e :=
  rfl

/-- The framed lifting is monotone in the normal and the exception postcondition. -/
theorem ownFWP_monotone {c : m α} {Φ Φ' : α → HeapProp Val} {e e' : E}
    (hΦ : ∀ a, Φ a ⊑ Φ' a) (he : e ⊑ e') : ownFWP own c Φ e ⊑ ownFWP own c Φ' e' :=
  @fwp_monotone (m α) α (HeapProp Val) E _ _ _ (ownWPInst own α) c Φ Φ' e e' hΦ he

/-- Return: the postcondition at `x` entails the framed lifting of `pure x`. -/
theorem le_ownFWP_pure (x : α) (Φ : α → HeapProp Val) (e : E) :
    Φ x ⊑ ownFWP own (pure x : m α) Φ e :=
  @le_fwp_pure m _ (HeapProp Val) E _ _ _ (ownWPMonad own) α x Φ e

/-- Lax bind for the framed lifting. -/
theorem ownFWP_bind_le (c : m α) (f : α → m β) (Φ : β → HeapProp Val) (e : E) :
    ownFWP own c (fun a => ownFWP own (f a) Φ e) e ⊑ ownFWP own (c >>= f) Φ e :=
  @fwp_bind_le m _ (HeapProp Val) E _ _ _ (ownWPMonad own) α β c f Φ e

/-- Frame: at the framed lifting every program frames every resource. -/
theorem ownFWP_frame (c : m α) (Φ : α → HeapProp Val) (e : E) (R : HeapProp Val) :
    iprop(ownFWP own c Φ e ∗ R) ⊑ ownFWP own c (fun a => iprop(Φ a ∗ R)) e := by
  have h := @fwp_frame (m α) α (HeapProp Val) E _ _ _ (ownWPInst own α) c Φ e R
  simp only [heapProp_sep_eq] at h
  exact h

/-- The framed lifting at a partial state `σ`: for every frame `F` and every state `σf` disjoint
from `σ` that satisfies `F`, the weakest precondition holds at every total state whose image is
`σ ∪ σf`, for the postcondition `Φ a ∗ F` read through `own`. -/
theorem ownFWP_apply (c : m α) (Φ : α → HeapProp Val) (e : E) (σ : State Val) :
    ownFWP own c Φ e σ ↔ ∀ (F : HeapProp Val) (σf : State Val), (σ || σf) → F σf →
      ∀ s, own s = σ ∪ σf → wp c (fun a s' => iprop(Φ a ∗ F) (own s')) e s := by
  have key := @le_fwp_iff (m α) α (HeapProp Val) E _ _ _ (ownWPInst own α) c Φ e
    (fun τ => τ = σ)
  simp only [heapProp_sep_eq] at key
  constructor
  · intro h F σf hd hF s hs
    exact key.1 (fun τ hτ => hτ ▸ h) F (σ ∪ σf) ⟨σ, σf, rfl, hd, rfl, hF⟩ s hs
  · intro h
    refine key.2 (fun F τ ⟨σ₁, σ₂, hτ, hd, h₁, h₂⟩ s hs => ?_) σ rfl
    subst h₁
    exact h F σ₂ hd h₂ s (hs.trans hτ)

end Own

/-! ## Instances -/

/-- The state monad over a weakest precondition monad at `Prop` (the toolchain's
`StateT.instWPMonad`) has a framed lifted weakest precondition at every embedding of its states,
and every program frames every resource. -/
example {T : Type u → Type v} [Monad T] {S : Type u} {E : Type z} [Assertion E]
    [WPMonad T Prop E] {Val : Type t} (own : S → State Val) {α : Type u} (c : StateT S T α)
    (Φ : α → HeapProp Val) (e : E) (R : HeapProp Val) :
    iprop(ownFWP (W := StateT.instWPMonad) own c Φ e ∗ R) ⊑
      ownFWP (W := StateT.instWPMonad) own c (fun a => iprop(Φ a ∗ R)) e :=
  ownFWP_frame (W := StateT.instWPMonad) own c Φ e R

/-- The framed lifted weakest precondition monad of a state monad. -/
noncomputable example {T : Type u → Type v} [Monad T] {S : Type u} {E : Type z} [Assertion E]
    [WPMonad T Prop E] {Val : Type t} (own : S → State Val) :
    WPMonad (StateT S T) (HeapProp Val) E :=
  ownFramedWPMonad (W := StateT.instWPMonad) own

end CatCrypt.Crypto.IrisBridge
