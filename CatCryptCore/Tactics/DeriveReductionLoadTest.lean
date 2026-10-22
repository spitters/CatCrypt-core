/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Crypto.UCConcrete

/-!
# Tests of `derive_reduction` on heap resets

Reductions that run a computation from a fixed heap: `fun _ => D b h₀` after a sample,
`SPComp.initHeap h₀` followed by an adversary, and the shapes of `dhDDHReduction` and
`Env.coreReduction` written with `fixHeap` over an environment `Z : Env α β`. Each is reflected
to a tree with a `SPTree.load` node; the compile equations are pinned by `example`s.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveReductionLoadTest

open CatCrypt.Core

/-- The distinguisher `D` run from the fixed heap `h₀` on a uniform bit (the shape of
`fixHeap h₀ D` after a sample). -/
noncomputable def fixRed (h₀ : Heap) (D : Bool → SPComp Bool) : SPComp Bool := do
  let b ← SPComp.sample Bool
  fun _ => D b h₀

derive_reduction fixRed

example (h₀ : Heap) (D : Bool → SPTree Bool) :
    (fixRed.tree h₀ D).compile = fixRed h₀ fun b => (D b).compile :=
  fixRed.compile_tree h₀ D

/-- The adversary `A` run after a reset of the heap to `h₀`. -/
noncomputable def initRed (h₀ : Heap) (A : SPComp Bool) : SPComp Bool :=
  SPComp.bind (CatCrypt.Crypto.SPComp.initHeap h₀) fun _ => A

derive_reduction initRed

example (h₀ : Heap) (A : SPTree Bool) :
    (initRed.tree h₀ A).compile = initRed h₀ A.compile :=
  initRed.compile_tree h₀ A

open CatCrypt.Crypto.UCConcrete (Env fixHeap)

/-- The shape of `dhDDHReduction`: the distinguisher of the environment `Z` on a triple, with
the heap fixed to `Z.heap`. -/
noncomputable def envRed {W α : Type} (Z : Env α (Unit ⊕ (W × W × W))) (x y z : W) :
    SPComp Bool :=
  fixHeap Z.heap Z.dist (Sum.inr (x, y, z))

derive_reduction envRed

/-- The shape of `Env.coreReduction`: a context around the core output `o`, then the
distinguisher of `Z`, with the heap fixed to `Z.heap`. -/
noncomputable def coreRed {α β γ ρ : Type} (pre : α → SPComp ρ)
    (k : α → ρ → γ → SPComp β) (Z : Env α β) : γ → SPComp Bool :=
  fixHeap Z.heap (fun o => SPComp.bind (pre Z.input)
    (fun r => SPComp.bind (k Z.input r o) Z.dist))

derive_reduction coreRed

end CatCrypt.Tactics.DeriveReductionLoadTest
