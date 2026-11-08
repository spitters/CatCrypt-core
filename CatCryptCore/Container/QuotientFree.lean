/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Core.SPTreeFree
public import PolyFun.PFunctor.Free.Quotient

/-!
# Free monads modulo an equational theory

`PolyFun.PFunctor.Free.Quotient` declares equational theories over a polynomial functor
(`PFunctor.EqTheory`), the free monad modulo a theory (`PFunctor.QFreeM`) and quotient containers
(`PFunctor.QContainer`). This module adds the instance on `SPTree`: `SPTree.sampleTheory` has the
commutation of two independent uniform samples and the discarding of an unused uniform sample,
over finite nonempty sample spaces. `SPTree.spHandler` validates it, so compilation into `SPComp`
factors through the quotient.

## Main definitions

* `CatCrypt.Core.SPTree.sampleTheory` — commutation and discarding of uniform samples

## Main results

* `CatCrypt.Core.SPTree.spHandler_validates` — `SPComp` validates the sampling theory
* `CatCrypt.Core.SPTree.compileQ_mk`, `CatCrypt.Core.SPTree.compile_eq_of_cong` — compilation
  factors through the quotient
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Core

open CatCrypt.Prob PFunctor

namespace SPTree

/-- The equations of uniform sampling: commutation of two independent samples and discarding
of an unused sample, over finite nonempty sample spaces. -/
inductive SampleEqn : Type 1
  /-- Sampling from `β` then from `γ` is sampling from `γ` then from `β`. -/
  | comm (β γ : Type) (finβ : Fintype β) (neβ : Nonempty β) (finγ : Fintype γ)
      (neγ : Nonempty γ)
  /-- Sampling from `β` and ignoring the outcome is the empty program. -/
  | discard (β : Type) (finβ : Fintype β) (neβ : Nonempty β)

/-- The context of a sampling equation. -/
def SampleEqn.ctx : SampleEqn → Type
  | .comm β γ .. => β × γ
  | .discard .. => PUnit

/-- The left-hand side of a sampling equation. -/
def SampleEqn.lhs : (e : SampleEqn) → SPTree.Sig.FreeM e.ctx
  | .comm β γ finβ neβ finγ neγ =>
    .liftBind (.sample β finβ neβ) fun b =>
      .liftBind (.sample γ finγ neγ) fun c => .pure ((b, c) : β × γ)
  | .discard β finβ neβ => .liftBind (.sample β finβ neβ) fun _ => .pure PUnit.unit

/-- The right-hand side of a sampling equation. -/
def SampleEqn.rhs : (e : SampleEqn) → SPTree.Sig.FreeM e.ctx
  | .comm β γ finβ neβ finγ neγ =>
    .liftBind (.sample γ finγ neγ) fun c =>
      .liftBind (.sample β finβ neβ) fun b => .pure ((b, c) : β × γ)
  | .discard .. => .pure PUnit.unit

/-- The sampling theory of `SPTree`. -/
def sampleTheory : EqTheory.{1, 0, 1} SPTree.Sig where
  Eqn := SampleEqn
  ctx := SampleEqn.ctx
  lhs := SampleEqn.lhs
  rhs := SampleEqn.rhs

/-- Compilation into `SPComp` validates the sampling theory: uniform samples over finite
nonempty types commute and an unused one is discarded. -/
theorem spHandler_validates : sampleTheory.Validates spHandler := by
  rintro (⟨β, γ, finβ, neβ, finγ, neγ⟩ | ⟨β, finβ, neβ⟩)
  · exact SPComp.isPure_bind_comm (SPComp.sample β) (SPComp.sample γ)
      (fun b c => SPComp.pure (b, c)) (SPComp.sample_isPure β) (SPComp.sample_isPure γ)
  · change SPComp.bind (SPComp.sample β) (fun _ => SPComp.pure PUnit.unit) =
      SPComp.pure PUnit.unit
    funext h
    simp only [SPComp.bind, SPComp.sample, SDistr.bind_assoc, SDistr.pure_bind]
    exact SDistr.uniform_bind_const _

/-- Compilation of the quotient of `SPTree.Sig.FreeM` by the sampling theory. -/
noncomputable def compileQ {α : Type} : QFreeM sampleTheory α → SPComp α :=
  QFreeM.lift spHandler spHandler_validates

/-- On the class of a tree, the compilation of the quotient is `compile`. -/
theorem compileQ_mk {α : Type} (s : SPTree α) : compileQ (QFreeM.mk (toFreeM s)) = s.compile :=
  compile_eq_liftM s

/-- Trees congruent under the sampling theory compile to the same computation. -/
theorem compile_eq_of_cong {α : Type} {s t : SPTree α}
    (h : sampleTheory.Cong (toFreeM s) (toFreeM t)) : s.compile = t.compile := by
  rw [← compileQ_mk, ← compileQ_mk, QFreeM.sound h]

/-! ## Test -/

/-- A discarded uniform sample compiles away. -/
example : (SPTree.sample Bool inferInstance inferInstance fun _ => .ret (0 : ℕ)).compile =
    (SPTree.ret 0).compile :=
  compile_eq_of_cong (.ax (T := sampleTheory) (.discard Bool inferInstance inferInstance)
    fun _ => FreeM.pure 0)

end SPTree

end CatCrypt.Core
