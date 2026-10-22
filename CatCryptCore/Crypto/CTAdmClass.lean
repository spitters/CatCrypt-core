/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCryptCore.Crypto.UCAdmClass
public import CatCryptCore.Core.SPTree
public import CatCryptCore.Crypto.MonadCostModel

/-!
# Constant-time programs as an admissibility class

This file defines an abstract constant-time predicate `CTClass`, closed under the monad
operations, and the admissibility class `UCAdmClass_of_CTClass` it induces. For `SPComp` it
defines the operation shape `SPShape` of a syntax tree (the tree with return values erased)
and the predicate `ct_spComp`: an arrow is constant-time when it is the compilation of a
family of syntax trees that all have one shape. It proves that `ct_spComp` holds for `pure`,
is closed under bind, and implies query-bounded admissibility (`spTreeQueryAdm`), since a
fixed shape fixes the query count.

## Main definitions

* `CTClass` — abstract constant-time predicate, closed under the monad operations
* `UCAdmClass_of_CTClass` — the admissibility class of constant-time arrows
* `SPShape` — `SPTree` with return values erased
* `SPTree.toShape` — the shape of an `SPTree`
* `ct_spComp` — constant-time predicate on `SPComp` arrows

## Main results

* `queryCost_eq_shape_queryCost`, `toShape_bind` — query cost and bind computed on shapes
* `ct_spComp_pure`, `ct_spComp_bind` — closure of `ct_spComp`
* `ct_spComp_implies_queryAdm` — constant-time arrows are query-bounded

Relation to the literature: `CatCryptCore/Crypto/Complexity.md`.

## References

* Barthe, Betarte, Campo, Luna, Pichardie, "System-Level Non-Interference for Constant-Time
  Cryptography", CCS 2014
* Barthe, Blazy, Grégoire, Hutin, Laporte, Pichardie, Trieu, "Formal Verification of a
  Constant-Time Preserving C Compiler", POPL 2020
-/

@[expose] public section

open scoped ENNReal

namespace UCMonad

/-! ## Section 1: Abstract Constant-Time Class -/

/-- Abstract constant-time predicate on Kleisli arrows.

    A program `f : α → T β` is constant-time if its observable execution
    pattern is independent of the input value. The axioms mirror `UCAdmClass`:
    - `ct_pure`: no operations → trivially CT
    - `ct_bind`: sequential CT programs compose to CT
    - `ct_mapSum`: public branching on sum tags preserves CT -/
class CTClass (T : Type → Type) [Monad T] [UCMonadBase T] where
  /-- Constant-time predicate. -/
  ct : {α β : Type} → (α → T β) → Prop
  /-- Pure is constant-time (no operations). -/
  ct_pure {α : Type} : ct (pure : α → T α)
  /-- Kleisli composition preserves constant-time. -/
  ct_bind {α β γ : Type} {f : α → T β} {g : β → T γ} :
    ct f → ct g → ct (fun a => f a >>= g)
  /-- Coproduct preserves constant-time (branching on public sum tag). -/
  ct_mapSum {α β γ δ : Type} {f : α → T β} {g : γ → T δ} :
    ct f → ct g → ct (UCMonadBase.ucMapSum f g)
  /-- Precomposition with a pure function preserves constant-time. -/
  ct_precomp {α α' β : Type} {g : α → T β} (f : α' → α) :
    ct g → ct (g ∘ f)

export CTClass (ct ct_pure ct_bind ct_mapSum ct_precomp)

/-- CT programs form a UCAdmClass.

    This is a `def`, not an `instance`, to avoid typeclass diamonds. -/
noncomputable def UCAdmClass_of_CTClass
    (T : Type → Type) [Monad T] [UCMonadBase T] [CTClass T] :
    UCAdmClass T where
  adm f := ct f
  adm_pure := ct_pure
  adm_bind := ct_bind
  adm_mapSum := ct_mapSum
  adm_precomp := ct_precomp

end UCMonad

/-! ## Section 2: SPTree Shapes -/

open CatCrypt.Core CatCrypt.Crypto

/-- SPTree with return values erased: captures the operation structure
    (which operations, in what order, with what branching) while
    forgetting the actual computed values. -/
inductive SPShape : Type 1 where
  | ret : SPShape
  | sample (β : Type) (finβ : Fintype β) (neβ : Nonempty β) :
      (β → SPShape) → SPShape
  | get (l : Location) : (l.ty → SPShape) → SPShape
  | set (l : Location) : SPShape → SPShape
  | fail : SPShape
  /-- A heap reset to a heap with `n` locations. -/
  | load (n : ℕ) : SPShape → SPShape

namespace SPShape

/-- Substitute a fixed shape at every `ret` node. -/
def bind : SPShape → SPShape → SPShape
  | .ret, s => s
  | .sample β finβ neβ k, s => .sample β finβ neβ (fun b => (k b).bind s)
  | .get l k, s => .get l (fun v => (k v).bind s)
  | .set l t, s => .set l (t.bind s)
  | .fail, _ => .fail
  | .load n t, s => .load n (t.bind s)

/-- Operation count at shape level. -/
def queryCost : SPShape → ℕ
  | .ret => 0
  | .sample β finβ _ k =>
    letI := finβ
    1 + Finset.univ.sup (fun b => (k b).queryCost)
  | .get l k => 1 + Finset.univ.sup (fun v => (k v).queryCost)
  | .set _ t => 1 + t.queryCost
  | .fail => 0
  | .load n t => 1 + n + t.queryCost

@[grind =] theorem bind_ret (s : SPShape) : s.bind .ret = s := by
  induction s with
  | ret => rfl
  | sample β finβ neβ k ih => simp only [bind]; congr_funext
  | get l k ih => simp only [bind]; congr_funext
  | set l t ih => simp only [bind]; congr_funext
  | fail => rfl
  | load n t ih => simp only [bind]; congr_funext

@[grind =] theorem bind_assoc (s₁ s₂ s₃ : SPShape) :
    (s₁.bind s₂).bind s₃ = s₁.bind (s₂.bind s₃) := by
  induction s₁ with
  | ret => rfl
  | sample β finβ neβ k ih => simp only [bind]; congr_funext
  | get l k ih => simp only [bind]; congr_funext
  | set l t ih => simp only [bind]; congr_funext
  | fail => rfl
  | load n t ih => simp only [bind]; congr_funext

end SPShape

namespace CatCrypt.Core.SPTree

variable {α β : Type}

/-- Extract the shape of an SPTree, erasing return values and set values. -/
def toShape : SPTree α → SPShape
  | .ret _ => .ret
  | .sample β finβ neβ k => .sample β finβ neβ (fun b => (k b).toShape)
  | .get l k => .get l (fun v => (k v).toShape)
  | .set l _ t => .set l t.toShape
  | .fail => .fail
  | .load h₀ t => .load h₀.data.keys.card t.toShape

/-- queryCost factors through toShape. -/
theorem queryCost_eq_shape_queryCost (s : SPTree α) :
    s.queryCost = s.toShape.queryCost := by
  induction s with
  | ret _ => rfl
  | sample β finβ neβ k ih =>
    simp only [SPTree.queryCost, toShape, SPShape.queryCost]
    congr 1; apply Finset.sup_congr rfl; intro b _; exact ih b
  | get l k ih =>
    simp only [SPTree.queryCost, toShape, SPShape.queryCost]
    congr 1; apply Finset.sup_congr rfl; intro v _; exact ih v
  | set l v t ih =>
    simp only [SPTree.queryCost, toShape, SPShape.queryCost]; exact congr_arg _ ih
  | fail => rfl
  | load h₀ t ih =>
    simp only [SPTree.queryCost, toShape, SPShape.queryCost]; exact congr_arg _ ih

/-- toShape commutes with bind when the continuation has constant shape. -/
theorem toShape_bind (s : SPTree α) (f : α → SPTree β) (sf : SPShape)
    (hf : ∀ a, (f a).toShape = sf) :
    (s.bind f).toShape = s.toShape.bind sf := by
  induction s with
  | ret a =>
    simp [SPTree.bind, toShape, SPShape.bind]; exact hf a
  | sample γ finγ neγ k ih =>
    simp only [SPTree.bind, toShape, SPShape.bind]; congr_funext
  | get l k ih =>
    simp only [SPTree.bind, toShape, SPShape.bind]; congr_funext
  | set l v t ih =>
    simp only [SPTree.bind, toShape, SPShape.bind]; congr_funext
  | fail =>
    simp [SPTree.bind, toShape, SPShape.bind]
  | load h₀ t ih =>
    simp only [SPTree.bind, toShape, SPShape.bind]; congr_funext

end CatCrypt.Core.SPTree

/-! ## Section 3: Concrete CT for SPComp -/

open CatCrypt.Core (SPTree SPComp Location)
open UCMonad

/-- A Kleisli arrow `f : α → SPComp β` is **constant-time** if there exists
    an SPTree representation where the shape is independent of the input.

    Strictly stronger than `spTreeQueryAdm`:
    - CT: entire operation pattern is input-independent
    - Query-bounded: only the operation count is bounded -/
def ct_spComp {α β : Type} (f : α → SPComp β) : Prop :=
  ∃ (s : α → SPTree β),
    (∀ a, (s a).compile = f a) ∧
    ∃ (shape : SPShape), ∀ a, (s a).toShape = shape

/-- CT implies query-bounded: constant shape implies constant cost. -/
theorem ct_spComp_implies_queryAdm {α β : Type} {f : α → SPComp β}
    (h : ct_spComp f) : spTreeQueryAdm.adm f := by
  obtain ⟨s, hs_compile, shape, hs_shape⟩ := h
  refine ⟨s, hs_compile, shape.queryCost, fun a => ?_⟩
  rw [SPTree.queryCost_eq_shape_queryCost, hs_shape]

/-- Pure is constant-time. -/
theorem ct_spComp_pure {α : Type} : ct_spComp (SPComp.pure : α → SPComp α) :=
  ⟨SPTree.ret, fun _ => rfl, .ret, fun _ => rfl⟩

/-- Kleisli composition preserves constant-time:
    if `f` and `g` have constant shapes `sf` and `sg`, then `f >=> g`
    has constant shape `sf.bind sg`. -/
theorem ct_spComp_bind {α β γ : Type} {f : α → SPComp β} {g : β → SPComp γ}
    (hf : ct_spComp f) (hg : ct_spComp g) :
    ct_spComp (fun a => SPComp.bind (f a) g) := by
  obtain ⟨sf, hsf, shapef, hshapef⟩ := hf
  obtain ⟨sg, hsg, shapeg, hshapeg⟩ := hg
  refine ⟨fun a => (sf a).bind sg, ?_, shapef.bind shapeg, ?_⟩
  · intro a
    rw [SPTree.compile_bind, hsf a]
    congr_funext
  · intro a
    rw [SPTree.toShape_bind (sf a) sg shapeg hshapeg, hshapef]

/-! ### Remark on `mapSum`

  The concrete predicate `ct_spComp` demands a **single** shape for **all** inputs.
  For `mapSum f g : (α ⊕ γ) → SPComp (β ⊕ δ)`, the `.inl` branch uses `shapef`
  and the `.inr` branch uses `shapeg`, which may differ.  Consequently,
  `ct_spComp_mapSum` is not provable in general — it holds only when both
  branches happen to share the same shape.

  In the information-flow formulation of CCS 2014 (§3, §4.1), branching is permitted on
  public (Low) data and forbidden on secret (High) data. `ct_mapSum` reads the sum tag
  as public. `ct_spComp` has no public inputs, so `mapSum` is CT for it only when the two
  branch shapes agree. The abstract `CTClass` takes `ct_mapSum` as an axiom; concrete
  instances may use predicates that track a public/secret partition.

  The abstract bridge `UCAdmClass_of_CTClass` remains the recommended path for
  obtaining admissibility from any CT predicate satisfying the three axioms. -/
