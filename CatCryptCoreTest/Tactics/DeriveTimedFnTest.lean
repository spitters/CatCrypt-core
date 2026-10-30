/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Crypto.UCTransparentMultiTimed
public import CatCryptCore.Crypto.AKE.ChannelSquare

/-!
# Tests of `derive_timed` and `derive_reduction` on optional and sampling shapes

Costed forms and erasure theorems of small trees and computations of three shapes, and of the
adversary-port simulator `secSimA` of `CatCryptCore.Crypto.AKE.ChannelSquare`:

* sampling from a general distribution: a tree with a `sampleDist` node (`drawTree`), a
  computation sampling twice from `liftSDistr μ` (`drawTwice`), and `secSimA`, which samples a
  transcript from `ofPMF μ` by `sampleFrom`; the time theorems of `drawTree` and of the three
  steps of `secSimA` are derived by `derive_time_bound`;
* a dispatch `Option.elim` with a function argument: on a tree (`optTree`) and on a computation
  (`optRun`, the shape of `optSim` of `CatCrypt.Crypto.GUCSquareGseq`);
* an optional value holding a function: a continuation stored in `Option (α → β)`, applied
  (`contApply`) and stored (`contStore`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimedFnTest

open CatCrypt.Core

/-! ## Sampling from a general distribution -/

/-- Sample from `μ` and return the sample. -/
def drawTree {β : Type} (μ : Prob.SDistr β) : SPTree β :=
  .sampleDist β μ fun b => .ret b

derive_timed drawTree

example {β : Type} (μ : Prob.SDistr β) : (drawTree.timed μ).2.erase = drawTree μ :=
  drawTree.erase_timed μ

derive_time_bound drawTree

/-- Sample twice from `μ` and return the pair. -/
noncomputable def drawTwice {β : Type} (μ : Prob.SDistr β) : SPComp (β × β) :=
  SPComp.bind (liftSDistr μ) fun a => SPComp.bind (liftSDistr μ) fun b => SPComp.pure (a, b)

derive_reduction drawTwice

example {β : Type} (μ : Prob.SDistr β) : (drawTwice.tree μ).compile = drawTwice μ :=
  drawTwice.compile_tree μ

/-! ## A dispatch on an optional value -/

/-- On `some s`, run `k s` and wrap its result; on `none`, return `none`. -/
def optTree {σ γ : Type} (k : σ → SPTree γ) (o : Option σ) : SPTree (Option γ) :=
  o.elim (.ret none) fun s => (k s).bind fun c => .ret (some c)

derive_timed optTree

/-- The shape of `optSim`: `S₁` on an optional answer, `none` staying `none`. -/
noncomputable def optRun {σ γ : Type} (S₁ : σ → SPComp γ) (o : Option σ) :
    SPComp (Option γ) :=
  o.elim (SPComp.pure none) fun s => SPComp.map some (S₁ s)

derive_reduction optRun

example {σ γ : Type} (S₁ : σ → SPTree γ) (o : Option σ) :
    (optRun.tree S₁ o).compile = optRun (fun s => (S₁ s).compile) o :=
  optRun.compile_tree S₁ o

/-! ## An optional value holding a function -/

/-- Apply a stored continuation to `a`, or return `none` when none is stored. -/
def contApply {α β : Type} (st : Option (α → β)) (a : α) : SPTree (Option β) :=
  match st with
  | none => .ret none
  | some f => .ret (some (f a))

derive_timed contApply

/-- Store the continuation `f`. -/
def contStore {α β : Type} (f : α → β) : SPTree (Option (α → β)) :=
  .ret (some f)

derive_timed contStore

end CatCrypt.Tactics.DeriveTimedFnTest

/-! ## The adversary-port simulator of the secure channel -/

derive_reduction CatCrypt.Crypto.AKE.ChannelSquare.secSimA
derive_time_bound CatCrypt.Crypto.AKE.ChannelSquare.secSimA.start.tree
derive_time_bound CatCrypt.Crypto.AKE.ChannelSquare.secSimA.resume.tree
derive_time_bound CatCrypt.Crypto.AKE.ChannelSquare.secSimA.finish.tree
