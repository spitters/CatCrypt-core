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
is `IsPure`, which the procedure does not perform. The removal of an unused binding by an
`IsPure` and mass-one computation and by a discard field, rewrites by a two-binding chain
fact (a field, or an argument) on adjacent and on separated key pairs, and a permutation
equation applied to the leaves.
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

/-- An unused `IsPure` binding of mass one is removed. -/
example {α β : Type} (p : SPComp α) (k : SPComp β) (hp : SPComp.IsPure p)
    (hl : ∀ h, CatCrypt.Prob.SDistr.mass (p h) = 1) :
    p.bind (fun _ => k) = k := by
  bind_swap_nf

/-- Without the mass-one fact the unused binding is kept. -/
example {α β : Type} (p : SPComp α) (k : SPComp β) (hp : SPComp.IsPure p)
    (hl : ∀ h, CatCrypt.Prob.SDistr.mass (p h) = 1) :
    p.bind (fun _ => k) = k := by
  fail_if_success (clear hl; bind_swap_nf)
  bind_swap_nf

/-- An unused binding in the middle of a chain is removed and the remaining bindings are
exchanged. -/
example {α β γ : Type} (p : SPComp α) (q : SPComp β) (r : SPComp γ)
    (k : α → γ → SPComp Bool) (hp : SPComp.IsPure p) (hq : SPComp.IsPure q)
    (hl : ∀ h, CatCrypt.Prob.SDistr.mass (q h) = 1) :
    p.bind (fun a => q.bind (fun _ => r.bind (fun c => k a c))) =
      r.bind (fun c => p.bind (fun a => k a c)) := by
  bind_swap_nf

/-- Abstract Diffie–Hellman dependencies: key generation, its `IsPure` and discard
fields, and the correctness of the shared value on two generated key pairs. -/
structure TDHDeps (K : Type) where
  /-- Key generation. -/
  keygen : SPComp (K × K)
  /-- Key generation does not touch the heap. -/
  keygen_isPure : SPComp.IsPure keygen
  /-- An unused key generation can be dropped. -/
  keygen_bind_discard : ∀ {β : Type} (rest : SPComp β),
    SPComp.bind keygen (fun _ => rest) = rest
  /-- The shared value. -/
  dh : K → K → K
  /-- Correctness of the shared value on generated key pairs. -/
  dh_keygen_comm : ∀ {α : Type} (f : K × K → K × K → K → SPComp α),
    (keygen.bind fun p => keygen.bind fun q => f p q (dh p.1 q.2)) =
      keygen.bind fun p => keygen.bind fun q => f p q (dh q.1 p.2)

/-- An unused key generation is removed by the discard field. -/
example {K : Type} (d : TDHDeps K) (A : K → SPComp Bool) :
    (do let ⟨_, _⟩ ← d.keygen; let ⟨b, gb⟩ ← d.keygen; A (d.dh b gb) : SPComp Bool) =
    (do let ⟨b, gb⟩ ← d.keygen; A (d.dh b gb)) := by
  bind_swap_nf

/-- The chain fact of `d` rewrites the shared value of two key pairs. -/
example {K : Type} (d : TDHDeps K) (A : K → K → K → SPComp Bool) :
    (do let ⟨a, ga⟩ ← d.keygen; let ⟨_b, gb⟩ ← d.keygen; A ga gb (d.dh a gb) : SPComp Bool) =
    (do let ⟨_a, ga⟩ ← d.keygen; let ⟨b, gb⟩ ← d.keygen; A ga gb (d.dh b ga)) := by
  bind_swap_nf

/-- The chain fact applies to key pairs separated by a sample and bound in another order on
the other side. -/
example {K : Type} [Fintype K] [Nonempty K] (d : TDHDeps K) (A : K → K → K → K → SPComp Bool) :
    (do let ⟨a, ga⟩ ← d.keygen; let s ← SPComp.sample K; let ⟨_b, gb⟩ ← d.keygen
        A ga gb s (d.dh a gb) : SPComp Bool) =
    (do let ⟨b, gb⟩ ← d.keygen; let ⟨_a, ga⟩ ← d.keygen; let s ← SPComp.sample K
        A ga gb s (d.dh b ga)) := by
  bind_swap_nf

/-- A chain fact given as an argument. -/
example {K : Type} (kg : SPComp (K × K)) (dh : K → K → K) (_hkg : SPComp.IsPure kg)
    (A : K → K → K → SPComp Bool)
    (hc : (∀ {α : Type} (f : K × K → K × K → K → SPComp α),
      (kg.bind fun p => kg.bind fun q => f p q (dh p.1 q.2)) =
        kg.bind fun p => kg.bind fun q => f p q (dh q.1 p.2)) ∧ True) :
    (kg.bind fun p => kg.bind fun q => A p.2 q.2 (dh p.1 q.2)) =
      kg.bind fun p => kg.bind fun q => A p.2 q.2 (dh q.1 p.2) := by
  fail_if_success bind_swap_nf
  bind_swap_nf [hc.1]

/-- A permutation equation given as an argument closes the leaves. -/
example {K : Type} (p q : SPComp K) (f : K → K → K) (hf : ∀ a b, f a b = f b a)
    (A : K → SPComp Bool) (hp : SPComp.IsPure p) :
    p.bind (fun a => q.bind (fun b => A (f a b))) =
      q.bind (fun b => p.bind (fun a => A (f b a))) := by
  fail_if_success bind_swap_nf
  bind_swap_nf [hf]

end CatCrypt.Tactic.BindSwapTest
