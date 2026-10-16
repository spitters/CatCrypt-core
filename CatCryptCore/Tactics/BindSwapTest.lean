/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.BindSwap
public meta import CatCryptCore.Tactics.BindSwap

/-!
# Tests for `bind_swap_nf`

Equalities of `SPComp` bind chains over abstract computations that differ by the order of
independent bindings: an `IsPure` computation exchanged with an arbitrary one, a
permutation of samples and key generations around an adversary call with pair patterns,
an `IsPure` fact given as an argument, and two exchanges of computations neither of which
is `IsPure`, which the procedure does not perform.
-/

set_option autoImplicit false

open CatCrypt.Core

namespace CatCrypt.Tactic.BindSwapTest

/-- An `IsPure` computation commutes with an arbitrary one. -/
example {α β γ : Type} (p : SPComp α) (q : SPComp β) (k : α → β → SPComp γ)
    (hp : SPComp.IsPure p) :
    p.bind (fun a => q.bind (fun b => k a b)) = q.bind (fun b => p.bind (fun a => k a b)) := by
  bind_swap_nf

/-- Abstract dependencies: a key generation with its `IsPure` field. -/
structure TDeps (K : Type) where
  /-- Key generation. -/
  keygen : SPComp (K × K)
  /-- Key generation does not touch the heap. -/
  keygen_isPure : SPComp.IsPure keygen

/-- Two key generations and a sample permuted around an adversary call, with pair
patterns; the `IsPure` facts are the field of `d` and the sample combinator. -/
example {K : Type} [Fintype K] [Nonempty K] [DecidableEq K] (d : TDeps K)
    (A : K → K → K → SPComp Bool) (adv : SPComp K) :
    (do let ⟨a, ga⟩ ← d.keygen; let s ← SPComp.sample K; let x ← adv; let ⟨b, gb⟩ ← d.keygen
        A ga gb (if s = x then a else b) : SPComp Bool) =
    (do let x ← adv; let ⟨b, gb⟩ ← d.keygen; let s ← SPComp.sample K; let ⟨a, ga⟩ ← d.keygen
        A ga gb (if s = x then a else b)) := by
  bind_swap_nf

/-- The `IsPure` fact of a computation passed as an argument. -/
example {α β γ : Type} (p : SPComp α) (q : SPComp β) (k : α → β → SPComp γ)
    (h : SPComp.IsPure q ∧ True) :
    p.bind (fun a => q.bind (fun b => k a b)) = q.bind (fun b => p.bind (fun a => k a b)) := by
  fail_if_success bind_swap_nf
  bind_swap_nf [h.1]

/-- A quantified `IsPure` hypothesis applies to a computation that depends on an earlier
binding which it is not exchanged with. -/
example {α β γ : Type} (p : SPComp α) (f : α → SPComp β) (r : SPComp γ)
    (k : α → β → γ → SPComp Bool) (hf : ∀ a, SPComp.IsPure (f a)) :
    p.bind (fun a => (f a).bind (fun b => r.bind (fun c => k a b c))) =
      p.bind (fun a => r.bind (fun c => (f a).bind (fun b => k a b c))) := by
  bind_swap_nf

/-- Two computations neither of which is `IsPure` are not exchanged. -/
example {α β γ : Type} (p : SPComp α) (q : SPComp β) (k : α → β → SPComp γ)
    (h : p.bind (fun a => q.bind (fun b => k a b)) = q.bind (fun b => p.bind (fun a => k a b))) :
    p.bind (fun a => q.bind (fun b => k a b)) = q.bind (fun b => p.bind (fun a => k a b)) := by
  fail_if_success bind_swap_nf
  exact h

end CatCrypt.Tactic.BindSwapTest
