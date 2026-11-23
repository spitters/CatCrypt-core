/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Bridges.IrisBridge.OwnWP
public import PolyFun.PFunctor.Free.WP.Upstream
public import CatCryptCore.Relational.RelationalQ0

/-!
# Instances of the ownership-lifted, framed weakest precondition

* Free monads of a polynomial functor, interpreted through a handler into a weakest precondition
  monad over state predicates (`PFunctor.FreeM.wpMonadOfHandler`), have a framed lifted weakest
  precondition at every embedding of the states, at which every program frames every resource.
* `LaxWPOver T ret bnd Pred`: a predicate transformer on `T` that is monotone and satisfies the lax
  return and bind laws for the operations `ret` and `bnd`, which need not form a lawful monad.
  Every weakest precondition monad gives one at each exception postcondition
  (`LaxWPOver.ofWPMonad`), and so does every graded relational lifting `RelQ0Lift T` through its
  diagonal `liftR 0 (fun a b => a = b ∧ φ a) m m` at `pure'` and `bind'` (`diagWP`).

## Search words

free monad, handler, polynomial functor, relational lifting, diagonal, lax weakest precondition
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.IrisBridge

open Std.WP Lean.Order RefinementWP
open Iris.Instances.Classical Iris.Instances.Data

universe v w z t uA uB

/-! ## Free monads through a handler -/

/-- The framed lifted weakest precondition monad of a free monad interpreted through a handler. -/
noncomputable example {P : PFunctor.{uA, uB}} {n : Type uB → Type w} [Monad n] {S : Type v}
    {E : Type z} [Assertion E] [WPMonad n (S → Prop) E] (s : PFunctor.Handler n P)
    {Val : Type t} (own : S → State Val) : WPMonad (PFunctor.FreeM P) (HeapProp Val) E :=
  ownFramedWPMonad (W := PFunctor.FreeM.wpMonadOfHandler s) own

/-- Every free program frames every resource at the framed lifted weakest precondition. -/
example {P : PFunctor.{uA, uB}} {n : Type uB → Type w} [Monad n] {S : Type v}
    {E : Type z} [Assertion E] [WPMonad n (S → Prop) E] (s : PFunctor.Handler n P)
    {Val : Type t} (own : S → State Val) {α : Type uB} (c : PFunctor.FreeM P α)
    (Φ : α → HeapProp Val) (e : E) (R : HeapProp Val) :
    iprop(ownFWP (W := PFunctor.FreeM.wpMonadOfHandler s) own c Φ e ∗ R) ⊑
      ownFWP (W := PFunctor.FreeM.wpMonadOfHandler s) own c (fun a => iprop(Φ a ∗ R)) e :=
  ownFWP_frame (W := PFunctor.FreeM.wpMonadOfHandler s) own c Φ e R

/-! ## Lax weakest preconditions over return and bind operations -/

/-- A predicate transformer on `T` that is monotone and satisfies the lax return and bind laws for
the operations `ret` and `bnd`. -/
structure LaxWPOver (T : Type → Type) (ret : ∀ {α : Type}, α → T α)
    (bnd : ∀ {α β : Type}, T α → (α → T β) → T β) (Pred : Type w) [Assertion Pred] where
  /-- The weakest precondition of a computation at a postcondition. -/
  wp : ∀ {α : Type}, T α → (α → Pred) → Pred
  /-- Monotonicity in the postcondition. -/
  wp_mono : ∀ {α : Type} (x : T α) {φ ψ : α → Pred}, φ ⊑ ψ → wp x φ ⊑ wp x ψ
  /-- Return: the postcondition at `a` entails the weakest precondition of `ret a`. -/
  pure_le : ∀ {α : Type} (a : α) (φ : α → Pred), φ a ⊑ wp (ret a) φ
  /-- Lax bind. -/
  bind_le : ∀ {α β : Type} (x : T α) (k : α → T β) (φ : β → Pred),
    wp x (fun a => wp (k a) φ) ⊑ wp (bnd x k) φ

/-- A weakest precondition monad at a fixed exception postcondition `e`. -/
def LaxWPOver.ofWPMonad (T : Type → Type) [Monad T] {Pred : Type w} {E : Type z}
    [Assertion Pred] [Assertion E] [WPMonad T Pred E] (e : E) :
    LaxWPOver T (fun a => pure a) (fun x k => x >>= k) Pred where
  wp x φ := WP.wp x φ e
  wp_mono _ _ _ h := WP.wp_monotone_post h
  pure_le a φ := WPMonad.pure_le_wp_pure a φ e
  bind_le x k φ := WPMonad.bind_le_wp_bind x k φ e

/-- The diagonal of a graded relational lifting at grade `0`: `φ` holds of `x` when `x` is related
to itself by equality of results satisfying `φ`. -/
def diagWP (T : Type → Type) [CatCrypt.RelQ0Lift T] :
    LaxWPOver T CatCrypt.RelQ0Lift.pure' CatCrypt.RelQ0Lift.bind' Prop where
  wp x φ := CatCrypt.RelQ0Lift.liftR 0 (fun a b => a = b ∧ φ a) x x
  wp_mono _ _ _ h hx := CatCrypt.RelQ0Lift.liftR_mono_rel
    (fun a _ hab => ⟨hab.1, h a hab.2⟩) hx
  pure_le _ _ h := CatCrypt.RelQ0Lift.liftR_pure ⟨rfl, h⟩
  bind_le _ _ _ h := by
    have := CatCrypt.RelQ0Lift.liftR_bind (ε := 0) (δ := 0) h
      (fun a b hab => by obtain ⟨rfl, hk⟩ := hab; exact hk)
    rwa [add_zero] at this

end CatCrypt.Crypto.IrisBridge
