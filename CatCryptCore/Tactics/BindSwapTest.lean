/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.BindSwap
public meta import CatCryptCore.Tactics.BindSwap
public import CatCryptCore.Crypto.Advantage

/-!
# Tests for `bind_swap_nf`, `bij_cov`, `spec_inline` and `le_of_eq_nf`

Equalities of `SPComp` bind chains over abstract computations that differ by the order of
independent bindings: an `IsPure` computation exchanged with an arbitrary one, a
permutation of samples and key generations around an adversary call with pair patterns,
an `IsPure` fact given as an argument, and two exchanges of computations neither of which
is `IsPure`, which the procedure does not perform. The removal of an unused binding by an
`IsPure` and mass-one computation and by a discard field, rewrites by a two-binding chain
fact (a field, or an argument) on adjacent and on separated key pairs, and a permutation
equation applied to the leaves. Definitions with an implicit type parameter and instance
arguments given as arguments and unfolded by name, and a sample of a product type aligned
with the samples of its components.

`bij_cov` (of `CatCryptCore.Tactics.BindVcgen`), `spec_inline` and `le_of_eq_nf` close
goals over the definitions of this file, directly and through `catcrypt_auto`, and fail on
a goal outside their shape (`fail_if_success`).
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

/-- A game over a word type `W` given by an implicit parameter and instance arguments. -/
noncomputable def tReal {W : Type} [Fintype W] [Nonempty W] (p : SPComp W)
    (A : W → W → SPComp Bool) : SPComp Bool :=
  p.bind fun a => (SPComp.sample W).bind fun b => A a b

/-- The game `tReal` with its two bindings exchanged. -/
noncomputable def tSwap {W : Type} [Fintype W] [Nonempty W] (p : SPComp W)
    (A : W → W → SPComp Bool) : SPComp Bool :=
  (SPComp.sample W).bind fun b => p.bind fun a => A a b

/-- Definitions given as arguments are unfolded by name, without `(W := W)`. -/
example {W : Type} [Fintype W] [Nonempty W] (p : SPComp W) (A : W → W → SPComp Bool) :
    tReal p A = tSwap p A := by
  fail_if_success bind_swap_nf
  bind_swap_nf [tReal, tSwap]

/-- A sample of a product type equals the samples of its components. -/
example {W : Type} [Fintype W] [Nonempty W] (A : W → W → SPComp Bool) :
    ((SPComp.sample (W × W)).bind fun ab => A ab.1 ab.2) =
      (SPComp.sample W).bind fun a => (SPComp.sample W).bind fun b => A a b := by
  bind_swap_nf

/-- A sample of a product type with a pair pattern equals the samples of its components
bound in the other order. -/
example {W : Type} [Fintype W] [Nonempty W] (A : W → W → SPComp Bool) :
    (do let ⟨a, b⟩ ← SPComp.sample (W × W); A a b : SPComp Bool) =
      (SPComp.sample W).bind fun b => (SPComp.sample W).bind fun a => A a b := by
  bind_swap_nf

@[expose] public section

/-! ## Change of variables through a bijection -/

/-- A family of bijections from keys to outputs, indexed by inputs. -/
structure BijFam where
  /-- Keys. -/
  K : Type
  /-- Inputs. -/
  I : Type
  /-- Outputs. -/
  O : Type
  [fK : Fintype K]
  [nK : Nonempty K]
  [fO : Fintype O]
  [nO : Nonempty O]
  /-- The bijection of each input. -/
  bij : I → (K ≃ O)

attribute [instance] BijFam.fK BijFam.nK BijFam.fO BijFam.nO

example (B : BijFam) (x : B.I) :
    (SPComp.sample B.K).bind (fun k => SPComp.pure (B.bij x k)) = SPComp.sample B.O := by
  bij_cov

example (B : BijFam) (x : B.I) :
    (SPComp.sample B.K).bind (fun k => SPComp.pure (B.bij x k)) = SPComp.sample B.O := by
  catcrypt_auto

example {K O : Type} [Fintype K] [Nonempty K] [Fintype O] [Nonempty O] (f : K → O)
    (hf : Function.Bijective f) (c : SPComp Bool) (g : Bool → O → SPComp ℕ) :
    c.bind (fun b => (SPComp.sample K).bind (fun k => g b (f k))) =
    c.bind (fun b => (SPComp.sample O).bind (fun o => g b o)) := by
  bij_cov

example (c : SPComp Bool) : c.bind (fun b => SPComp.pure b) = c := by
  fail_if_success bij_cov
  simp

/-! ## Inlining a specification of an abstract operation -/

/-- A three-move protocol with a simulator, over abstract operations. -/
structure Proto where
  /-- Statements. -/
  St : Type
  /-- Witnesses. -/
  Wi : Type
  /-- First messages. -/
  Msg : Type
  /-- Challenges. -/
  Ch : Type
  /-- Responses. -/
  Rsp : Type
  [fCh : Fintype Ch]
  [nCh : Nonempty Ch]
  /-- The relation. -/
  rel : St → Wi → Prop
  [dec : ∀ x w, Decidable (rel x w)]
  /-- The first message. -/
  commit : St → Wi → SPComp Msg
  /-- The response. -/
  respond : St → Wi → Msg → Ch → SPComp Rsp
  /-- The simulator of a transcript with a given challenge. -/
  simulate : St → Ch → SPComp (Msg × Rsp)

attribute [instance] Proto.fCh Proto.nCh Proto.dec

/-- The honest transcript, or `none` outside the relation. -/
noncomputable def pReal (sp : Proto) :
    sp.St × sp.Wi → SPComp (Option (sp.Msg × sp.Ch × sp.Rsp)) :=
  fun ⟨x, w⟩ =>
    if sp.rel x w then do
      let a ← sp.commit x w
      let e ← SPComp.sample sp.Ch
      let z ← sp.respond x w a e
      SPComp.pure (some (a, e, z))
    else SPComp.pure none

/-- The simulated transcript, or `none` outside the relation. -/
noncomputable def pIdeal (sp : Proto) :
    sp.St × sp.Wi → SPComp (Option (sp.Msg × sp.Ch × sp.Rsp)) :=
  fun ⟨x, w⟩ =>
    if sp.rel x w then do
      let e ← SPComp.sample sp.Ch
      let (a, z) ← sp.simulate x e
      SPComp.pure (some (a, e, z))
    else SPComp.pure none

example (sp : Proto)
    (hzk : ∀ x w e, sp.rel x w →
      (do let a ← sp.commit x w; let z ← sp.respond x w a e; SPComp.pure (a, z)) =
        sp.simulate x e)
    (x : sp.St) (w : sp.Wi) :
    pReal sp (x, w) = pIdeal sp (x, w) := by
  unfold pReal pIdeal
  spec_inline

example (sp : Proto)
    (hzk : ∀ x w e, sp.rel x w →
      (do let a ← sp.commit x w; let z ← sp.respond x w a e; SPComp.pure (a, z)) =
        sp.simulate x e)
    (x : sp.St) (w : sp.Wi) :
    pReal sp (x, w) = pIdeal sp (x, w) := by
  unfold pReal pIdeal
  catcrypt_auto

example {C D N : Type} [Fintype C] [Nonempty C] [Fintype D] [Nonempty D]
    (mk : N → SPComp (N × C)) (g : D → N)
    (h : ∀ n, (SPComp.sample C).bind (fun c => SPComp.pure (n, c)) = mk n) :
    (SPComp.sample D).bind (fun d => mk (g d)) =
    (SPComp.sample C).bind (fun c => (SPComp.sample D).bind fun d => SPComp.pure (g d, c)) := by
  spec_inline

example (c : SPComp Bool) : c.bind (fun b => SPComp.pure b) = c := by
  fail_if_success spec_inline
  simp

/-- The continuation that runs `f` on a right injection and passes a left one through. -/
noncomputable def mapS {α β : Type} (f : α → SPComp β) : Unit ⊕ α → SPComp (Unit ⊕ β)
  | .inl u => SPComp.pure (.inl u)
  | .inr a => (f a).bind fun b => SPComp.pure (.inr b)

/-- Unfolding lemma of `mapS` at a left injection. -/
theorem mapS_inl {α β : Type} (f : α → SPComp β) (u : Unit) :
    mapS f (.inl u) = SPComp.pure (.inl u) := rfl

/-- Unfolding lemma of `mapS` at a right injection. -/
theorem mapS_inr {α β : Type} (f : α → SPComp β) (a : α) :
    mapS f (.inr a) = (f a).bind fun b => SPComp.pure (.inr b) := rfl

/-- The honest transcript as a right injection, or a left one outside the relation. -/
noncomputable def pRealS (sp : Proto) :
    sp.St × sp.Wi → SPComp (Unit ⊕ (sp.Msg × sp.Ch × sp.Rsp)) :=
  fun ⟨x, w⟩ =>
    if sp.rel x w then do
      let a ← sp.commit x w
      let e ← SPComp.sample sp.Ch
      let z ← sp.respond x w a e
      SPComp.pure (.inr (a, e, z))
    else SPComp.pure (.inl ())

/-- The statement as a right injection, or a left one outside the relation. -/
noncomputable def pIdealS (sp : Proto) : sp.St × sp.Wi → SPComp (Unit ⊕ sp.St) :=
  fun ⟨x, w⟩ => if sp.rel x w then SPComp.pure (.inr x) else SPComp.pure (.inl ())

/-- The simulator: a simulated transcript passed to `A`. -/
noncomputable def pSim (sp : Proto) {V : Type} (A : sp.Msg × sp.Ch × sp.Rsp → SPComp V) :
    sp.St → SPComp V := fun x => do
  let e ← SPComp.sample sp.Ch
  let (a, z) ← sp.simulate x e
  A (a, e, z)

example (sp : Proto)
    (hzk : ∀ x w e, sp.rel x w →
      (do let a ← sp.commit x w; let z ← sp.respond x w a e; SPComp.pure (a, z)) =
        sp.simulate x e)
    (x : sp.St) (w : sp.Wi) (V : Type) (A : sp.Msg × sp.Ch × sp.Rsp → SPComp V) :
    (pRealS sp (x, w)).bind (mapS A) = (pIdealS sp (x, w)).bind (mapS (pSim sp A)) := by
  unfold pRealS pIdealS pSim
  spec_inline [mapS_inl, mapS_inr]

example (sp : Proto)
    (hzk : ∀ x w e, sp.rel x w →
      (do let a ← sp.commit x w; let z ← sp.respond x w a e; SPComp.pure (a, z)) =
        sp.simulate x e)
    (x : sp.St) (w : sp.Wi) (V : Type) (A : sp.Msg × sp.Ch × sp.Rsp → SPComp V) :
    (pRealS sp (x, w)).bind (mapS A) = (pIdealS sp (x, w)).bind (mapS (pSim sp A)) := by
  unfold pRealS pIdealS pSim
  catcrypt_auto

/-! ## An advantage bound between equal games -/

section Advantage

open CatCrypt.Crypto

/-- Two operations, the first of them heap-independent, and a deterministic combiner. -/
structure TwoOps where
  /-- First results. -/
  P : Type
  /-- Second results. -/
  C : Type
  /-- Outputs. -/
  S : Type
  [fC : Fintype C]
  [nC : Nonempty C]
  /-- The first operation. -/
  op₁ : SPComp P
  /-- The first operation does not touch the heap. -/
  op₁_isPure : SPComp.IsPure op₁
  /-- The second operation. -/
  op₂ : SPComp C
  /-- The combiner. -/
  core : P → C → S

attribute [instance] TwoOps.fC TwoOps.nC

/-- Both operations run. -/
noncomputable def gReal (c : TwoOps) : SPComp c.S :=
  c.op₁.bind fun p => c.op₂.bind fun q => SPComp.pure (c.core p q)

/-- The second operation replaced by a uniform sample. -/
noncomputable def gHyb (c : TwoOps) : SPComp c.S :=
  c.op₁.bind fun p => (SPComp.sample c.C).bind fun q => SPComp.pure (c.core p q)

/-- The advantage of `A` against the second operation. -/
noncomputable def advOp₂ (c : TwoOps) (A : c.C → SPComp Bool) : ENNReal :=
  AdvantageA c.op₂ (SPComp.sample c.C) A

/-- The reduction: run the first operation and the distinguisher on the combination. -/
noncomputable def redOp₂ (c : TwoOps) (D : c.S → SPComp Bool) : c.C → SPComp Bool :=
  fun q => c.op₁.bind fun p => D (c.core p q)

example (c : TwoOps) (D : c.S → SPComp Bool) :
    AdvantageA (gReal c) (gHyb c) D ≤ advOp₂ c (redOp₂ c D) := by
  le_of_eq_nf

example (c : TwoOps) (D : c.S → SPComp Bool) :
    AdvantageA (gReal c) (gHyb c) D ≤ advOp₂ c (redOp₂ c D) := by
  catcrypt_auto

example (c : TwoOps) (D : c.S → SPComp Bool) :
    AdvantageA (gHyb c) (gReal c) D ≤ advOp₂ c (redOp₂ c D) := by
  le_of_eq_nf

example (a b : ENNReal) (h : a ≤ b) : a ≤ b := by
  fail_if_success le_of_eq_nf
  exact h

end Advantage

end

end CatCrypt.Tactic.BindSwapTest
