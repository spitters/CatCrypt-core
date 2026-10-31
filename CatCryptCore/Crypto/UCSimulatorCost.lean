/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCSimulator
public import CatCryptCore.Crypto.UCSimulatorMapPorts
public import CatCryptCore.Crypto.UCTransparentMultiTimed
public import CatCryptCore.Crypto.UCInterleaveCost

/-!
# Costed bundled simulators

`Simulator.Timed`, the costed mirror of the bundled simulators `Simulator` of
`UCSimulator.lean` built from opaque multi-call simulators by sequential composition: a costed
simulator is a costed multi-call simulator (`Simulator.Timed.ofMultiHybrid`, a value of
`MultiHybrid.Timed`) or the composite of two costed simulators (`Simulator.Timed.comp`). The
mirror carries no opacity proofs, so erasure is a relation (`Simulator.Timed.Erases`): a costed
multi-call simulator erases to `Simulator.ofMultiHybrid π h` for every `π` it erases to and every
opacity proof `h`, and a costed composite erases to the composite of erasures of its parts.

The time bound `Simulator.Timed.TimeBound T t` bounds each step of the costed multi-call
simulators of `T` (a `start`, `resume` or `finish` step, with the cost of building its tree) by
the parts of `t`: the time of a costed multi-call simulator is the largest bound of its steps,
the time of a composite the sum of the times of its parts. The costed tensor
`Simulator.tensor.timed` is the costed multi-call simulator of the costed tensor
`MultiHybrid.Timed.tensor`, and its time is that of the tensor's steps.

## Main definitions

* `Simulator.Timed`, `Simulator.Timed.Erases`, `Simulator.Timed.TimeBound`: costed simulators,
  their erasure relation and their time bound.
* `Simulator.tensor.timed`: the costed tensor of costed multi-call simulators.

## Main results

* `Simulator.ofMultiHybrid.erase_timed`, `Simulator.ofMultiHybrid.timeBound_timed`: a costed
  multi-call simulator erases to the bundled simulator, and its time is the largest bound of
  its steps.
* `Simulator.comp.erase_timed`, `Simulator.comp.timeBound_timed`: erasure of a costed
  composite, and its time, the sum of the times of the parts.
* `Simulator.tensor.erase_timed`, `Simulator.tensor.timeBound_timed`: erasure of the costed
  tensor, and its time, the larger bounds of the steps of the components plus `7` or `3`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core

/-- The time bound of a costed multi-call simulator on the states of the invariant `Inv`: the
initial state satisfies `Inv`, every step from a state of `Inv` returns states of `Inv`, and
its `start`, `resume` and `finish` steps from a state of `Inv` cost at most `a`, `b`, `c`. -/
def MultiHybrid.Timed.TimeBoundInv {σ E O EG OG : Type} (A : MultiHybrid.Timed σ E O EG OG)
    (Inv : σ → Prop) (a b c : ℕ) : Prop :=
  Inv A.init ∧
  (∀ s e, Inv s → SPTree.Timed.stepTime (A.startCost s e, A.start s e) ≤ a ∧
    SPTree.Timed.AllRet (fun y => Inv y.1) (A.start s e)) ∧
  (∀ s o, Inv s → SPTree.Timed.stepTime (A.resumeCost s o, A.resume s o) ≤ b ∧
    SPTree.Timed.AllRet (fun y => Inv y.1) (A.resume s o)) ∧
  (∀ s o, Inv s → SPTree.Timed.stepTime (A.finishCost s o, A.finish s o) ≤ c ∧
    SPTree.Timed.AllRet (fun y => Inv y.1) (A.finish s o))

/-- A time bound on every state is a time bound on the states of the invariant `True`. -/
theorem MultiHybrid.Timed.TimeBoundInv.of_timeBound {σ E O EG OG : Type}
    {A : MultiHybrid.Timed σ E O EG OG} {a b c : ℕ} (h : A.TimeBound a b c) :
    A.TimeBoundInv (fun _ => True) a b c :=
  ⟨trivial, fun s e _ => ⟨h.1 s e, SPTree.Timed.allRet_of_forall (fun _ => trivial) _⟩,
    fun s o _ => ⟨h.2.1 s o, SPTree.Timed.allRet_of_forall (fun _ => trivial) _⟩,
    fun s o _ => ⟨h.2.2 s o, SPTree.Timed.allRet_of_forall (fun _ => trivial) _⟩⟩

/-- A costed simulator from `(EG, OG)` with view `W` to `(E, O)` with view `V`: a costed
multi-call simulator, a costed multi-call simulator on costed states and events with the erasure
maps of its state and ports, the composite of two costed simulators through a middle interface
with view `U`, or a costed simulator on outer ports relabelled by `f` and `g`. -/
inductive Simulator.Timed : (E O EG OG : Type) → PubView E O → PubView EG OG → Type 1
  /-- A costed multi-call simulator. -/
  | ofMultiHybrid {σ E O EG OG : Type} {V : PubView E O} {W : PubView EG OG}
      (πT : MultiHybrid.Timed σ E O EG OG) : Simulator.Timed E O EG OG V W
  /-- A costed multi-call simulator on the costed state `σHat` and costed events, with the
  erasure maps of the state and of the four ports. -/
  | ofMultiHybridHat {σ σHat E EHat O OHat EG EGHat OG OGHat : Type} {V : PubView E O}
      {W : PubView EG OG} (εσ : σHat → σ) (εE : EHat → E) (εO : OHat → O) (εEG : EGHat → EG)
      (εOG : OGHat → OG) (πT : MultiHybrid.Timed σHat EHat OHat EGHat OGHat) :
      Simulator.Timed E O EG OG V W
  /-- The composite of the costed simulators `T₁` and `T₂`. -/
  | comp {E O EM OM EG OG : Type} {V : PubView E O} {U : PubView EM OM} {W : PubView EG OG}
      (T₁ : Simulator.Timed E O EM OM V U) (T₂ : Simulator.Timed EM OM EG OG U W) :
      Simulator.Timed E O EG OG V W
  /-- The costed simulator `T` on outer ports relabelled by `f` and `g`. -/
  | mapPorts {E O EM OM EG OG : Type} {V : PubView E O} {U : PubView EM OM} {W : PubView EG OG}
      (T : Simulator.Timed EM OM EG OG U W) (f : E → EM) (g : OM → O) :
      Simulator.Timed E O EG OG V W

namespace Simulator.Timed

/-- Erasure of a costed simulator. A costed multi-call simulator erases to
`Simulator.ofMultiHybrid π h` for each `π` it erases to and each opacity proof `h`, through the
erasure maps for one on costed states; a costed composite erases to the composite of erasures
of its parts; a relabelled one to the relabelling of an erasure of its simulator. -/
def Erases : {E O EG OG : Type} → {V : PubView E O} → {W : PubView EG OG} →
    Simulator.Timed E O EG OG V W → Simulator E O EG OG V W → Prop
  | _, _, _, _, V, W, .ofMultiHybrid (σ := σ) πT, S =>
    ∃ (π : MultiHybrid σ _ _ _ _) (h : π.Opaque V W), πT.Erases π ∧
      S = Simulator.ofMultiHybrid π h
  | _, _, _, _, V, W, .ofMultiHybridHat (σ := σ) (σHat := σHat) (EHat := EHat) (OHat := OHat)
      (EGHat := EGHat) (OGHat := OGHat) εσ εE εO εEG εOG πT, S =>
    ∃ (π : MultiHybrid σ _ _ _ _) (h : π.Opaque V W),
      MultiHybrid.Timed.ErasesHat σHat EHat OHat EGHat OGHat εσ εE εO εEG εOG πT π ∧
      S = Simulator.ofMultiHybrid π h
  | _, _, _, _, _, _, .comp T₁ T₂, S =>
    ∃ S₁ S₂, Erases T₁ S₁ ∧ Erases T₂ S₂ ∧ S = S₁.comp S₂
  | _, _, _, _, V, _, .mapPorts (U := U) T f g, S =>
    ∃ S₀ hf hg, Erases T S₀ ∧ S = Simulator.mapPorts (V := V) (U := U) S₀ f g hf hg

/-- The time bound `t` of a costed simulator: each step of a costed multi-call simulator costs
at most `t`, from every state, or from the states of an invariant for one on costed states;
the parts of a costed composite have time bounds whose sum is at most `t`; a relabelled
simulator has the time bound of its simulator. -/
def TimeBound : {E O EG OG : Type} → {V : PubView E O} → {W : PubView EG OG} →
    Simulator.Timed E O EG OG V W → ℕ → Prop
  | _, _, _, _, _, _, .ofMultiHybrid πT, t => πT.TimeBound t t t
  | _, _, _, _, _, _, .ofMultiHybridHat (σHat := σHat) _ _ _ _ _ πT, t =>
    ∃ Inv : σHat → Prop, πT.TimeBoundInv Inv t t t
  | _, _, _, _, _, _, .comp T₁ T₂, t => ∃ t₁ t₂, TimeBound T₁ t₁ ∧ TimeBound T₂ t₂ ∧ t₁ + t₂ ≤ t
  | _, _, _, _, _, _, .mapPorts T _ _, t => TimeBound T t

/-- A time bound of a costed simulator is a time bound of every larger time. -/
theorem TimeBound.mono {E O EG OG : Type} {V : PubView E O} {W : PubView EG OG}
    {T : Simulator.Timed E O EG OG V W} {t t' : ℕ} (h : T.TimeBound t) (ht : t ≤ t') :
    T.TimeBound t' := by
  induction T generalizing t t' with
  | ofMultiHybrid πT =>
    exact ⟨fun s e => le_trans (h.1 s e) ht, fun s o => le_trans (h.2.1 s o) ht,
      fun s o => le_trans (h.2.2 s o) ht⟩
  | ofMultiHybridHat εσ εE εO εEG εOG πT =>
    obtain ⟨Inv, h0, h1, h2, h3⟩ := h
    exact ⟨Inv, h0, fun s e hs => ⟨le_trans (h1 s e hs).1 ht, (h1 s e hs).2⟩,
      fun s o hs => ⟨le_trans (h2 s o hs).1 ht, (h2 s o hs).2⟩,
      fun s o hs => ⟨le_trans (h3 s o hs).1 ht, (h3 s o hs).2⟩⟩
  | mapPorts T f g ih => exact ih h ht
  | comp T₁ T₂ _ _ =>
    obtain ⟨t₁, t₂, h₁, h₂, hle⟩ := h
    exact ⟨t₁, t₂, h₁, h₂, by omega⟩

end Simulator.Timed

namespace Simulator

variable {σ σ' E O E' O' EM OM EG OG EG' OG' : Type} {V : PubView E O} {U : PubView EM OM}
  {W : PubView EG OG} {V' : PubView E' O'} {W' : PubView EG' OG'}

/-- **Erasure of a costed multi-call simulator**: a costed multi-call simulator that erases to
`π` erases to the bundled simulator `Simulator.ofMultiHybrid π h`. -/
theorem ofMultiHybrid.erase_timed {π : MultiHybrid σ E O EG OG}
    {πT : MultiHybrid.Timed σ E O EG OG} (hT : πT.Erases π) (h : π.Opaque V W) :
    (Simulator.Timed.ofMultiHybrid πT : Simulator.Timed E O EG OG V W).Erases
      (Simulator.ofMultiHybrid π h) :=
  ⟨π, h, hT, rfl⟩

/-- **Running time of a costed multi-call simulator**: if its steps cost at most `a`, `b`, `c`,
the costed simulator has the time bound `max a (max b c)`. -/
theorem ofMultiHybrid.timeBound_timed {πT : MultiHybrid.Timed σ E O EG OG} {a b c : ℕ}
    (hT : πT.TimeBound a b c) :
    (Simulator.Timed.ofMultiHybrid πT : Simulator.Timed E O EG OG V W).TimeBound
      (max a (max b c)) :=
  ⟨fun s e => le_trans (hT.1 s e) (by omega), fun s o => le_trans (hT.2.1 s o) (by omega),
    fun s o => le_trans (hT.2.2 s o) (by omega)⟩

section Hat

variable {σHat EHat OHat EGHat OGHat : Type}

/-- **Erasure of a costed multi-call simulator on costed states**: one that erases to `π`
through the erasure maps erases to the bundled simulator `Simulator.ofMultiHybrid π h`. -/
theorem ofMultiHybridHat.erase_timed {π : MultiHybrid σ E O EG OG}
    {εσ : σHat → σ} {εE : EHat → E} {εO : OHat → O} {εEG : EGHat → EG} {εOG : OGHat → OG}
    {πT : MultiHybrid.Timed σHat EHat OHat EGHat OGHat}
    (hT : MultiHybrid.Timed.ErasesHat σHat EHat OHat EGHat OGHat εσ εE εO εEG εOG πT π)
    (h : π.Opaque V W) :
    (Simulator.Timed.ofMultiHybridHat εσ εE εO εEG εOG πT : Simulator.Timed E O EG OG V W).Erases
      (Simulator.ofMultiHybrid π h) :=
  ⟨π, h, hT, rfl⟩

/-- **Running time of a costed multi-call simulator on costed states**: if its steps cost at
most `a`, `b`, `c` from the states of an invariant, it has the time bound `max a (max b c)`. -/
theorem ofMultiHybridHat.timeBound_timed {εσ : σHat → σ} {εE : EHat → E} {εO : OHat → O}
    {εEG : EGHat → EG} {εOG : OGHat → OG} {πT : MultiHybrid.Timed σHat EHat OHat EGHat OGHat}
    {Inv : σHat → Prop} {a b c : ℕ} (hT : πT.TimeBoundInv Inv a b c) :
    (Simulator.Timed.ofMultiHybridHat εσ εE εO εEG εOG πT : Simulator.Timed E O EG OG V W).TimeBound
      (max a (max b c)) :=
  ⟨Inv, hT.1, fun s e hs => ⟨le_trans (hT.2.1 s e hs).1 (by omega), (hT.2.1 s e hs).2⟩,
    fun s o hs => ⟨le_trans (hT.2.2.1 s o hs).1 (by omega), (hT.2.2.1 s o hs).2⟩,
    fun s o hs => ⟨le_trans (hT.2.2.2 s o hs).1 (by omega), (hT.2.2.2 s o hs).2⟩⟩

end Hat

/-- **Erasure of a relabelled costed simulator**: a costed simulator that erases to `S`,
relabelled by `f` and `g`, erases to `S.mapPorts f g hf hg`. -/
theorem mapPorts.erase_timed {S : Simulator EM OM EG OG U W} {T : Simulator.Timed EM OM EG OG U W}
    (hT : T.Erases S) (f : E → EM) (g : OM → O) (hf : ∀ e e', V.ev e e' → U.ev (f e) (f e'))
    (hg : ∀ o o', U.out o o' → V.out (g o) (g o')) :
    (Simulator.Timed.mapPorts T f g : Simulator.Timed E O EG OG V W).Erases
      (S.mapPorts f g hf hg) :=
  ⟨S, hf, hg, hT, rfl⟩

/-- **Running time of a relabelled costed simulator**: the time of its simulator. -/
theorem mapPorts.timeBound_timed {T : Simulator.Timed EM OM EG OG U W} {t : ℕ}
    (hT : T.TimeBound t) (f : E → EM) (g : OM → O) :
    (Simulator.Timed.mapPorts T f g : Simulator.Timed E O EG OG V W).TimeBound t :=
  hT

/-- **Erasure of a costed composite**: the composite of costed simulators that erase to `S₁`
and `S₂` erases to `S₁.comp S₂`. -/
theorem comp.erase_timed {S₁ : Simulator E O EM OM V U} {S₂ : Simulator EM OM EG OG U W}
    {T₁ : Simulator.Timed E O EM OM V U} {T₂ : Simulator.Timed EM OM EG OG U W}
    (h₁ : T₁.Erases S₁) (h₂ : T₂.Erases S₂) : (T₁.comp T₂).Erases (S₁.comp S₂) :=
  ⟨S₁, S₂, h₁, h₂, rfl⟩

/-- **Running time of a costed composite**: the sum of the times of its parts. -/
theorem comp.timeBound_timed {T₁ : Simulator.Timed E O EM OM V U}
    {T₂ : Simulator.Timed EM OM EG OG U W} {t₁ t₂ : ℕ} (h₁ : T₁.TimeBound t₁)
    (h₂ : T₂.TimeBound t₂) : (T₁.comp T₂).TimeBound (t₁ + t₂) :=
  ⟨t₁, t₂, h₁, h₂, le_rfl⟩

/-- The costed tensor of the costed multi-call simulators `πT` and `π'T`: the costed
multi-call simulator `MultiHybrid.Timed.tensor π π' πT π'T`. -/
noncomputable def tensor.timed (π : MultiHybrid σ E O EG OG) (π' : MultiHybrid σ' E' O' EG' OG')
    (πT : MultiHybrid.Timed σ E O EG OG) (π'T : MultiHybrid.Timed σ' E' O' EG' OG') :
    Simulator.Timed (E ⊕ E') (O ⊕ O') (EG ⊕ EG') (OG ⊕ OG') (V.sum V') (W.sum W') :=
  .ofMultiHybrid (MultiHybrid.Timed.tensor π π' πT π'T)

/-- **Erasure of the costed tensor**: the costed tensor of costed multi-call simulators that
erase to `π` and `π'` erases to `Simulator.tensor π π' h h'`. -/
theorem tensor.erase_timed {π : MultiHybrid σ E O EG OG} {π' : MultiHybrid σ' E' O' EG' OG'}
    {πT : MultiHybrid.Timed σ E O EG OG} {π'T : MultiHybrid.Timed σ' E' O' EG' OG'}
    (hT : πT.Erases π) (hT' : π'T.Erases π') (h : π.Opaque V W) (h' : π'.Opaque V' W') :
    (tensor.timed π π' πT π'T).Erases (Simulator.tensor π π' h h') :=
  ofMultiHybrid.erase_timed (MultiHybrid.Timed.tensor_erases hT hT') (h.tensor h')

/-- **Running time of the costed tensor**: if the steps of `πT` cost at most `a`, `b`, `c` and
those of `π'T` at most `a'`, `b'`, `c'`, the costed tensor has the time bound of the larger
start and resume bounds plus `7` and the larger finish bound plus `3`. -/
theorem tensor.timeBound_timed (π : MultiHybrid σ E O EG OG) (π' : MultiHybrid σ' E' O' EG' OG')
    {πT : MultiHybrid.Timed σ E O EG OG} {π'T : MultiHybrid.Timed σ' E' O' EG' OG'}
    {a b c a' b' c' : ℕ} (hT : πT.TimeBound a b c) (hT' : π'T.TimeBound a' b' c') :
    (tensor.timed (V := V) (W := W) (V' := V') (W' := W') π π' πT π'T).TimeBound
      (max (max a a' + 7) (max (max b b' + 7) (max c c' + 3))) :=
  ofMultiHybrid.timeBound_timed (MultiHybrid.Timed.tensor_timeBound π π' hT hT')

end Simulator

end CatCrypt.Crypto.UCTransparent
