/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCSimulatorCostPot
public import CatCryptCore.Crypto.UCSimulatorCostMono

/-!
# Potential time bounds of costed simulators under composition

The potential time bound `Simulator.Timed.TimeBoundPot T gE gO hEG hO a b` of a costed
simulator, by recursion on `T`: a costed multi-call simulator has a potential time bound
(`MultiHybrid.Timed.PotentialBound`) with the imports `gE`, `gO` received and `hEG`, `hO`
passed on; the factors of a costed composite have potential time bounds that conserve import at
the middle interface up to `κ` per message, the composite potential being the sum of the
potentials of the factors; a relabelled simulator has the potential time bound of its simulator
at imports the relabelling does not increase. One outer activation of a composite passes at most
`Simulator.Timed.msgBound` messages across its inner interfaces, so its potential grows by at
most `κ * msgBound` beyond the import received, which enters the constant `a`.

The certificate `Simulator.Timed.PotCert T a b c` is a potential time bound with no import
passed on at the outer ports and import measures linear in the size (`ImportLinear`). The
constant, graded and size-graded time bounds of costed simulators are potential time bounds,
the size-graded one when the composites are built with the size `0` on the middle answers
(`Simulator.Timed.TimeBoundSizedZero`). A costed simulator at other views has the potential time
bounds of the costed simulator.

The potential time bound `Hybrid.Timed.PotentialBound A gE gO hEG hO a b` of a costed one-call
hybrid machine is the one-call form of `MultiHybrid.Timed.PotentialBound`, with a `pre` and a
`post` clause; the costed one-call multi-call hybrid `Hybrid.Timed.ofHybrid π A` has it at the
constant `a + 1`. A machine whose steps cost at most `a + b * g x` on the input `x` has it with the
potential `0`; a machine that runs the `post` step of `A` followed by a continuation whose cost is
linear in the import that `A` passes on has it with the potential of `A`, since that import is
bounded by the potential clause of `A`.

## Main definitions

* `Simulator.Timed.calls`, `Simulator.Timed.msgBound`, `Simulator.Timed.msgSum`: the number of
  inner events per activation, the number of messages across inner interfaces per activation,
  and the sum of the latter over the composites of a costed simulator.
* `Simulator.Timed.TimeBoundPot`, `Simulator.Timed.PotCert`: the potential time bound and the
  potential certificate of a costed simulator.
* `Simulator.Timed.TimeBoundSizedZero`: the size-graded time bound with the size `0` on the
  answers of the inner factor of every composite.
* `MultiHybrid.Timed.PotentialBound.mono`: a potential time bound at larger constants and
  received imports and smaller imports passed on.
* `Hybrid.Timed.PotentialBound`: the potential time bound of a costed one-call hybrid machine;
  `Hybrid.Timed.PotentialBound.ofStepBound`, `Hybrid.Timed.PotentialBound.wrapPost`: the
  potential time bound of a step bound linear in the import and of a wrapped machine.
* `Hybrid.Timed.ofHybrid`, `Hybrid.Timed.PotentialBound.ofHybrid`: the costed one-call
  multi-call hybrid and its potential time bound.

## Main results

* `Simulator.ofMultiHybrid.timeBoundPot_timed`, `Simulator.ofMultiHybridHat.timeBoundPot_timed`,
  `Simulator.comp.timeBoundPot_timed`, `Simulator.mapPorts.timeBoundPot_timed`,
  `Simulator.tensor.timeBoundPot_timed`: the constructor rules.
* `Simulator.mono.timeBoundPot_timed`, `Simulator.mono.calls`, `Simulator.mono.msgBound`: a
  costed simulator at other views.
* `Hybrid.Timed.ofHybrid_erases`: erasure of the costed one-call multi-call hybrid.
* `Simulator.Timed.TimeBoundPot.mono`: monotonicity in the constants and imports.
* `Simulator.Timed.TimeBound.timeBoundPot`, `Simulator.Timed.TimeBoundGraded.timeBoundPot`,
  `Simulator.Timed.TimeBoundSizedZero.timeBoundPot`: the instances, and their certificates
  `Simulator.Timed.TimeBound.potCert`, `Simulator.Timed.TimeBoundGraded.potCert`,
  `Simulator.Timed.TimeBoundSizedZero.potCert`.
-/

@[expose] public section

set_option autoImplicit false

derive_reduction CatCrypt.Crypto.UCTransparent.MultiHybrid.ofHybrid


namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core

namespace MultiHybrid.Timed.PotentialBound

variable {σ E O EG OG : Type} {A : MultiHybrid.Timed σ E O EG OG} {gE : E → ℕ} {gO : OG → ℕ}
  {hEG : EG → ℕ} {hO : O → ℕ} {a b : ℕ}

/-- `Sum.elim` of pointwise smaller measures is pointwise smaller. -/
theorem sum_elim_le {hEG hEG' : EG → ℕ} {hO hO' : O → ℕ} (hhEG : ∀ g, hEG' g ≤ hEG g)
    (hhO : ∀ o, hO' o ≤ hO o) (z : EG ⊕ O) : Sum.elim hEG' hO' z ≤ Sum.elim hEG hO z := by
  cases z <;> simp [hhEG, hhO]

/-- A potential time bound is a potential time bound at larger constants, larger imports
received and smaller imports passed on, with the same invariant and potential. -/
def mono (P : A.PotentialBound gE gO hEG hO a b) {gE' : E → ℕ} {gO' : OG → ℕ}
    {hEG' : EG → ℕ} {hO' : O → ℕ} {a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b')
    (hgE : ∀ e, gE e ≤ gE' e) (hgO : ∀ o, gO o ≤ gO' o) (hhEG : ∀ g, hEG' g ≤ hEG g)
    (hhO : ∀ o, hO' o ≤ hO o) : A.PotentialBound gE' gO' hEG' hO' a' b' where
  Inv := P.Inv
  Φ := P.Φ
  init := P.init
  start s e hs := by
    refine ⟨le_trans (P.start s e hs).1
      (Nat.add_le_add ha (Nat.mul_le_mul hb (Nat.add_le_add_left (hgE e) _))),
      SPTree.Timed.allRet_mono (fun y hy => ⟨hy.1, ?_⟩) _ (P.start s e hs).2⟩
    have := sum_elim_le hhEG hhO y.2
    have := hgE e
    omega
  resume s o hs := by
    refine ⟨le_trans (P.resume s o hs).1
      (Nat.add_le_add ha (Nat.mul_le_mul hb (Nat.add_le_add_left (hgO o) _))),
      SPTree.Timed.allRet_mono (fun y hy => ⟨hy.1, ?_⟩) _ (P.resume s o hs).2⟩
    have := sum_elim_le hhEG hhO y.2
    have := hgO o
    omega
  finish s o hs := by
    refine ⟨le_trans (P.finish s o hs).1
      (Nat.add_le_add ha (Nat.mul_le_mul hb (Nat.add_le_add_left (hgO o) _))),
      SPTree.Timed.allRet_mono (fun y hy => ⟨hy.1, ?_⟩) _ (P.finish s o hs).2⟩
    have := hhO y.2
    have := hgO o
    omega

end MultiHybrid.Timed.PotentialBound

namespace Simulator.Timed

/-- The number of inner events of one activation of a costed simulator: `fuel + 1` for a costed
multi-call simulator, the product for a composite, that of its simulator for a relabelling. -/
def calls : {E O EG OG : Type} → {V : PubView E O} → {W : PubView EG OG} →
    Simulator.Timed E O EG OG V W → ℕ
  | _, _, _, _, _, _, .ofMultiHybrid πT => πT.fuel + 1
  | _, _, _, _, _, _, .ofMultiHybridHat _ _ _ _ _ πT => πT.fuel + 1
  | _, _, _, _, _, _, .comp T₁ T₂ => calls T₁ * calls T₂
  | _, _, _, _, _, _, .mapPorts T _ _ => calls T

/-- The number of messages across the inner interfaces of a costed simulator in one outer
activation: `0` for a costed multi-call simulator; for a composite, those of the outer factor,
and for each of its `calls` middle events the event, its answer and the messages of one
activation of the inner factor; for a relabelling, those of its simulator. -/
def msgBound : {E O EG OG : Type} → {V : PubView E O} → {W : PubView EG OG} →
    Simulator.Timed E O EG OG V W → ℕ
  | _, _, _, _, _, _, .ofMultiHybrid _ => 0
  | _, _, _, _, _, _, .ofMultiHybridHat _ _ _ _ _ _ => 0
  | _, _, _, _, _, _, .comp T₁ T₂ => msgBound T₁ + calls T₁ * (2 + msgBound T₂)
  | _, _, _, _, _, _, .mapPorts T _ _ => msgBound T

/-- The sum of `msgBound` over the composites of a costed simulator. -/
def msgSum : {E O EG OG : Type} → {V : PubView E O} → {W : PubView EG OG} →
    Simulator.Timed E O EG OG V W → ℕ
  | _, _, _, _, _, _, .ofMultiHybrid _ => 0
  | _, _, _, _, _, _, .ofMultiHybridHat _ _ _ _ _ _ => 0
  | _, _, _, _, _, _, .comp T₁ T₂ => msgSum T₁ + msgSum T₂ + msgBound (T₁.comp T₂)
  | _, _, _, _, _, _, .mapPorts T _ _ => msgSum T

/-- The potential time bound of a costed simulator with the import `gE` of its outer events and
`gO` of the answers it receives, the import `hEG` of its inner events and `hO` of its outer
outputs passed on, and the constants `a`, `b`. A costed multi-call simulator has a potential time
bound, through the erasure maps of the ports for one on costed events. The outer factor of a
composite has a potential time bound with the import `gM` of the middle answers it receives and
`hEM` of the middle events it passes on, the inner factor one with the import `gEM` of the
middle events it receives and `hM` of the middle answers it passes on; the middle interface
conserves import up to `κ` per message (`gEM ≤ hEM + κ`, `gM ≤ hM + κ`), and the constants
satisfy `a₁ + a₂ + (b₁ + b₂) * κ * msgBound ≤ a` and `b₁ + b₂ ≤ b`. A relabelled simulator has
the potential time bound of its simulator at imports the relabelling does not increase. -/
def TimeBoundPot : {E O EG OG : Type} → {V : PubView E O} → {W : PubView EG OG} →
    Simulator.Timed E O EG OG V W → (E → ℕ) → (OG → ℕ) → (EG → ℕ) → (O → ℕ) → ℕ → ℕ → Prop
  | _, _, _, _, _, _, .ofMultiHybrid πT, gE, gO, hEG, hO, a, b =>
    Nonempty (πT.PotentialBound gE gO hEG hO a b)
  | _, _, _, _, _, _, .ofMultiHybridHat _ εE εO εEG εOG πT, gE, gO, hEG, hO, a, b =>
    Nonempty (πT.PotentialBound (fun e => gE (εE e)) (fun o => gO (εOG o))
      (fun g => hEG (εEG g)) (fun o => hO (εO o)) a b)
  | _, _, _, _, _, _, .comp (EM := EM) (OM := OM) T₁ T₂, gE, gO, hEG, hO, a, b =>
    ∃ (κ : ℕ) (gM hM : OM → ℕ) (gEM hEM : EM → ℕ) (a₁ b₁ a₂ b₂ : ℕ),
      TimeBoundPot T₁ gE gM hEM hO a₁ b₁ ∧ TimeBoundPot T₂ gEM gO hEG hM a₂ b₂ ∧
      (∀ m, gEM m ≤ hEM m + κ) ∧ (∀ o, gM o ≤ hM o + κ) ∧
      a₁ + a₂ + (b₁ + b₂) * κ * msgBound (T₁.comp T₂) ≤ a ∧ b₁ + b₂ ≤ b
  | _, _, _, _, _, _, .mapPorts (EM := EM) (OM := OM) T f g, gE, gO, hEG, hO, a, b =>
    ∃ (gM : EM → ℕ) (hM : OM → ℕ), (∀ e, gM (f e) ≤ gE e) ∧ (∀ o, hO (g o) ≤ hM o) ∧
      TimeBoundPot T gM gO hEG hM a b

/-- The potential certificate `a`, `b`, `c` of a costed simulator: a potential time bound with
constants `a`, `b`, no import passed on at the outer ports, and import measures at most `c` times
the size of the message. -/
def PotCert {E O EG OG : Type} {V : PubView E O} {W : PubView EG OG} [ImportSize E]
    [ImportSize OG] (T : Simulator.Timed E O EG OG V W) (a b c : ℕ) : Prop :=
  ∃ (gE : E → ℕ) (gO : OG → ℕ), T.TimeBoundPot gE gO 0 0 a b ∧ ImportLinear gE gO c

/-- A potential time bound of a costed simulator is a potential time bound at larger constants,
larger imports received and smaller imports passed on. -/
theorem TimeBoundPot.mono {E O EG OG : Type} {V : PubView E O} {W : PubView EG OG}
    {T : Simulator.Timed E O EG OG V W} {gE gE' : E → ℕ} {gO gO' : OG → ℕ} {hEG hEG' : EG → ℕ}
    {hO hO' : O → ℕ} {a b a' b' : ℕ} (h : T.TimeBoundPot gE gO hEG hO a b) (ha : a ≤ a')
    (hb : b ≤ b') (hgE : ∀ e, gE e ≤ gE' e) (hgO : ∀ o, gO o ≤ gO' o)
    (hhEG : ∀ g, hEG' g ≤ hEG g) (hhO : ∀ o, hO' o ≤ hO o) :
    T.TimeBoundPot gE' gO' hEG' hO' a' b' := by
  induction T generalizing a b a' b' with
  | ofMultiHybrid πT =>
    obtain ⟨P⟩ := h
    exact ⟨P.mono ha hb hgE hgO hhEG hhO⟩
  | ofMultiHybridHat εσ εE εO εEG εOG πT =>
    obtain ⟨P⟩ := h
    exact ⟨P.mono ha hb (fun e => hgE (εE e)) (fun o => hgO (εOG o)) (fun g => hhEG (εEG g))
      (fun o => hhO (εO o))⟩
  | mapPorts T f g ih =>
    obtain ⟨gM, hM, hf, hg, hT⟩ := h
    exact ⟨gM, hM, fun e => (hf e).trans (hgE e), fun o => (hhO (g o)).trans (hg o),
      ih hT ha hb (fun _ => le_rfl) hgO hhEG (fun _ => le_rfl)⟩
  | comp T₁ T₂ ih₁ ih₂ =>
    obtain ⟨κ, gM, hM, gEM, hEM, a₁, b₁, a₂, b₂, h₁, h₂, hE, hA, h3, h4⟩ := h
    exact ⟨κ, gM, hM, gEM, hEM, a₁, b₁, a₂, b₂,
      ih₁ h₁ le_rfl le_rfl hgE (fun _ => le_rfl) (fun _ => le_rfl) hhO,
      ih₂ h₂ le_rfl le_rfl (fun _ => le_rfl) hgO hhEG (fun _ => le_rfl), hE, hA, by omega,
      by omega⟩

/-- A time bound `t` of a costed simulator is a potential time bound with no import, the
constant `t` and no growth. -/
theorem TimeBound.timeBoundPot {E O EG OG : Type} {V : PubView E O} {W : PubView EG OG}
    {T : Simulator.Timed E O EG OG V W} {t : ℕ} (h : T.TimeBound t) :
    T.TimeBoundPot 0 0 0 0 t 0 := by
  induction T generalizing t with
  | ofMultiHybrid πT =>
    exact ⟨(MultiHybrid.Timed.TimeBoundInv.of_timeBound h).potentialBound.mono (by omega)
      le_rfl (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl)⟩
  | ofMultiHybridHat εσ εE εO εEG εOG πT =>
    obtain ⟨Inv, hI⟩ := h
    exact ⟨hI.potentialBound.mono (by omega) le_rfl (fun _ => le_rfl) (fun _ => le_rfl)
      (fun _ => le_rfl) (fun _ => le_rfl)⟩
  | mapPorts T f g ih => exact ⟨0, 0, fun _ => le_rfl, fun _ => le_rfl, ih h⟩
  | comp T₁ T₂ ih₁ ih₂ =>
    obtain ⟨t₁, t₂, h₁, h₂, hle⟩ := h
    exact ⟨0, 0, 0, 0, 0, t₁, 0, t₂, 0, ih₁ h₁, ih₂ h₂, fun _ => le_rfl, fun _ => le_rfl,
      by simpa using hle, le_rfl⟩

/-- A graded time bound `a`, `b` of a costed simulator is a potential time bound with the import
`1` of every message, the constants `a + b * msgSum` and `b`, and the composites conserving
import up to `1` per message. -/
theorem TimeBoundGraded.timeBoundPot {E O EG OG : Type} {V : PubView E O} {W : PubView EG OG}
    {T : Simulator.Timed E O EG OG V W} {a b : ℕ} (h : T.TimeBoundGraded a b) :
    T.TimeBoundPot 1 1 0 0 (a + b * T.msgSum) b := by
  induction T generalizing a b with
  | ofMultiHybrid πT =>
    obtain ⟨Inv, hI⟩ := h
    exact ⟨hI.potentialBound.mono (Nat.le_add_right _ _) le_rfl (fun _ => le_rfl)
      (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl)⟩
  | ofMultiHybridHat εσ εE εO εEG εOG πT =>
    obtain ⟨Inv, hI⟩ := h
    exact ⟨hI.potentialBound.mono (Nat.le_add_right _ _) le_rfl (fun _ => le_rfl)
      (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl)⟩
  | mapPorts T f g ih => exact ⟨1, 0, fun _ => le_rfl, fun _ => le_rfl, ih h⟩
  | comp T₁ T₂ ih₁ ih₂ =>
    obtain ⟨a₁, b₁, a₂, b₂, h₁, h₂, h3, h4⟩ := h
    refine ⟨1, 1, 0, 1, 0, _, _, _, _, ih₁ h₁, ih₂ h₂, fun _ => le_rfl, fun _ => le_rfl, ?_,
      h4⟩
    have := Nat.mul_le_mul_right T₁.msgSum (show b₁ ≤ b by omega)
    have := Nat.mul_le_mul_right T₂.msgSum (show b₂ ≤ b by omega)
    have := Nat.mul_le_mul_right (T₁.comp T₂).msgBound h4
    simp only [msgSum, Nat.mul_one, Nat.mul_add] at *
    omega

/-- The size-graded time bound `a`, `b`, `c` of a costed simulator built with the size `0` on
the answers of the inner factor of every composite: as `TimeBoundSized`, with the outer factor
of a composite bounded at the size `0` on the middle answers. -/
def TimeBoundSizedZero : {E O EG OG : Type} → {V : PubView E O} → {W : PubView EG OG} →
    Simulator.Timed E O EG OG V W → (E → ℕ) → (OG → ℕ) → ℕ → ℕ → ℕ → Prop
  | _, _, _, _, _, _, .ofMultiHybrid (σ := σ) πT, sE, sO, a, b, c =>
    ∃ Inv : ℕ → σ → Prop, πT.TimeBoundSized Inv sE sO a b c
  | _, _, _, _, _, _, .ofMultiHybridHat (σHat := σHat) _ εE _ _ εOG πT, sE, sO, a, b, c =>
    ∃ Inv : ℕ → σHat → Prop,
      πT.TimeBoundSized Inv (fun e => sE (εE e)) (fun o => sO (εOG o)) a b c
  | _, _, _, _, _, _, .comp T₁ T₂, sE, sO, a, b, c =>
    ∃ (a₁ b₁ c₁ a₂ b₂ c₂ : ℕ), TimeBoundSizedZero T₁ sE (fun _ => 0) a₁ b₁ c₁ ∧
      TimeBoundSizedZero T₂ (fun _ => 0) sO a₂ b₂ c₂ ∧ a₁ + a₂ ≤ a ∧ b₁ + b₂ ≤ b ∧ c₁ + c₂ ≤ c
  | _, _, _, _, _, _, .mapPorts T f _, sE, sO, a, b, c =>
    ∃ sM, (∀ e, sM (f e) ≤ sE e) ∧ TimeBoundSizedZero T sM sO a b c

/-- A size-graded time bound with the size `0` on the middle answers is a size-graded time
bound. -/
theorem TimeBoundSizedZero.timeBoundSized {E O EG OG : Type} {V : PubView E O}
    {W : PubView EG OG} {T : Simulator.Timed E O EG OG V W} {sE : E → ℕ} {sO : OG → ℕ}
    {a b c : ℕ} (h : T.TimeBoundSizedZero sE sO a b c) : T.TimeBoundSized sE sO a b c := by
  induction T generalizing a b c with
  | ofMultiHybrid πT => exact h
  | ofMultiHybridHat εσ εE εO εEG εOG πT => exact h
  | mapPorts T f g ih =>
    obtain ⟨sM, hM, hT⟩ := h
    exact ⟨sM, hM, ih hT⟩
  | comp T₁ T₂ ih₁ ih₂ =>
    obtain ⟨a₁, b₁, c₁, a₂, b₂, c₂, h₁, h₂, h3, h4, h5⟩ := h
    exact ⟨fun _ => 0, a₁, b₁, c₁, a₂, b₂, c₂, ih₁ h₁, ih₂ h₂, AnswerSizeLe.zero T₂, h3, h4, h5⟩

/-- A size-graded time bound `a`, `b`, `c` of a costed simulator built with the size `0` on the
middle answers is a potential time bound with the import `1 + sE e` of an event and `1 + sO o`
of an answer, the constants `a + (b + c) * msgSum` and `b + c`, and the composites conserving
import up to `1` per message. -/
theorem TimeBoundSizedZero.timeBoundPot {E O EG OG : Type} {V : PubView E O}
    {W : PubView EG OG} {T : Simulator.Timed E O EG OG V W} {sE : E → ℕ} {sO : OG → ℕ}
    {a b c : ℕ} (h : T.TimeBoundSizedZero sE sO a b c) :
    T.TimeBoundPot (fun e => 1 + sE e) (fun o => 1 + sO o) 0 0 (a + (b + c) * T.msgSum)
      (b + c) := by
  induction T generalizing a b c with
  | ofMultiHybrid πT =>
    obtain ⟨Inv, hI⟩ := h
    exact ⟨hI.potentialBound.mono (Nat.le_add_right _ _) (by omega) (fun _ => le_rfl)
      (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl)⟩
  | ofMultiHybridHat εσ εE εO εEG εOG πT =>
    obtain ⟨Inv, hI⟩ := h
    exact ⟨hI.potentialBound.mono (Nat.le_add_right _ _) (by omega) (fun _ => le_rfl)
      (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl)⟩
  | mapPorts T f g ih =>
    obtain ⟨sM, hM, hT⟩ := h
    exact ⟨fun e => 1 + sM e, 0, fun e => Nat.add_le_add_left (hM e) 1, fun _ => le_rfl, ih hT⟩
  | comp T₁ T₂ ih₁ ih₂ =>
    obtain ⟨a₁, b₁, c₁, a₂, b₂, c₂, h₁, h₂, h3, h4, h5⟩ := h
    refine ⟨1, _, 0, _, 0, _, _, _, _, ih₁ h₁, ih₂ h₂, fun _ => le_rfl, fun _ => le_rfl, ?_,
      by omega⟩
    have := Nat.mul_le_mul_right T₁.msgSum (show b₁ + c₁ ≤ b + c by omega)
    have := Nat.mul_le_mul_right T₂.msgSum (show b₂ + c₂ ≤ b + c by omega)
    have := Nat.mul_le_mul_right (T₁.comp T₂).msgBound
      (show b₁ + c₁ + (b₂ + c₂) ≤ b + c by omega)
    simp only [msgSum, Nat.mul_one, Nat.mul_add] at *
    omega

/-- The potential certificate of a time bound `t`: the constants `t`, `0`, for every `c`. -/
theorem TimeBound.potCert {E O EG OG : Type} {V : PubView E O} {W : PubView EG OG}
    [ImportSize E] [ImportSize OG] {T : Simulator.Timed E O EG OG V W} {t : ℕ}
    (h : T.TimeBound t) (c : ℕ) : T.PotCert t 0 c :=
  ⟨0, 0, h.timeBoundPot, fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩

/-- The potential certificate of a graded time bound `a`, `b`: the constants `a + b * msgSum`,
`b` and `1`. -/
theorem TimeBoundGraded.potCert {E O EG OG : Type} {V : PubView E O} {W : PubView EG OG}
    [ImportSize E] [ImportSize OG] {T : Simulator.Timed E O EG OG V W} {a b : ℕ}
    (h : T.TimeBoundGraded a b) : T.PotCert (a + b * T.msgSum) b 1 :=
  ⟨1, 1, h.timeBoundPot, ImportLinear.one⟩

/-- The potential certificate of a size-graded time bound built with the size `0` on the middle
answers, with sizes `sE`, `sO` at most `c₀` times the message size: the constants
`a + (b + c) * msgSum`, `b + c` and `1 + c₀`. -/
theorem TimeBoundSizedZero.potCert {E O EG OG : Type} {V : PubView E O} {W : PubView EG OG}
    [ImportSize E] [ImportSize OG] {T : Simulator.Timed E O EG OG V W} {sE : E → ℕ}
    {sO : OG → ℕ} {a b c c₀ : ℕ} (h : T.TimeBoundSizedZero sE sO a b c)
    (hE : ∀ e, sE e ≤ c₀ * ImportSize.size e) (hO : ∀ o, sO o ≤ c₀ * ImportSize.size o) :
    T.PotCert (a + (b + c) * T.msgSum) (b + c) (1 + c₀) :=
  ⟨_, _, h.timeBoundPot, ImportLinear.one_add hE hO⟩

end Simulator.Timed

namespace Simulator

variable {σ σ' E O E' O' EM OM EG OG EG' OG' : Type} {V : PubView E O} {U : PubView EM OM}
  {W : PubView EG OG} {V' : PubView E' O'} {W' : PubView EG' OG'}

/-- **Potential running time of a costed multi-call simulator**: a potential time bound of its
steps is a potential time bound of the costed simulator. -/
theorem ofMultiHybrid.timeBoundPot_timed {πT : MultiHybrid.Timed σ E O EG OG} {gE : E → ℕ}
    {gO : OG → ℕ} {hEG : EG → ℕ} {hO : O → ℕ} {a b : ℕ}
    (P : πT.PotentialBound gE gO hEG hO a b) :
    (Simulator.Timed.ofMultiHybrid πT : Simulator.Timed E O EG OG V W).TimeBoundPot gE gO hEG hO
      a b :=
  ⟨P⟩

/-- **Potential running time of a costed multi-call simulator on costed states**: a potential
time bound of its steps at the imports through the erasure maps of the ports is a potential time
bound of the costed simulator. -/
theorem ofMultiHybridHat.timeBoundPot_timed {σHat EHat OHat EGHat OGHat : Type}
    {εσ : σHat → σ} {εE : EHat → E} {εO : OHat → O} {εEG : EGHat → EG} {εOG : OGHat → OG}
    {πT : MultiHybrid.Timed σHat EHat OHat EGHat OGHat} {gE : E → ℕ} {gO : OG → ℕ}
    {hEG : EG → ℕ} {hO : O → ℕ} {a b : ℕ}
    (P : πT.PotentialBound (fun e => gE (εE e)) (fun o => gO (εOG o)) (fun g => hEG (εEG g))
      (fun o => hO (εO o)) a b) :
    (Simulator.Timed.ofMultiHybridHat εσ εE εO εEG εOG πT :
      Simulator.Timed E O EG OG V W).TimeBoundPot gE gO hEG hO a b :=
  ⟨P⟩

/-- **Potential running time of a costed composite**: if the middle interface conserves import
up to `κ` per message, the composite has the potential time bound with the constants
`a₁ + a₂ + (b₁ + b₂) * κ * msgBound` and `b₁ + b₂`, and the sum of the potentials of its
factors. -/
theorem comp.timeBoundPot_timed {T₁ : Simulator.Timed E O EM OM V U}
    {T₂ : Simulator.Timed EM OM EG OG U W} {gE : E → ℕ} {gM hM : OM → ℕ} {gEM hEM : EM → ℕ}
    {gO : OG → ℕ} {hEG : EG → ℕ} {hO : O → ℕ} {κ a₁ b₁ a₂ b₂ : ℕ}
    (h₁ : T₁.TimeBoundPot gE gM hEM hO a₁ b₁) (h₂ : T₂.TimeBoundPot gEM gO hEG hM a₂ b₂)
    (hE : ∀ m, gEM m ≤ hEM m + κ) (hA : ∀ o, gM o ≤ hM o + κ) :
    (T₁.comp T₂).TimeBoundPot gE gO hEG hO (a₁ + a₂ + (b₁ + b₂) * κ * (T₁.comp T₂).msgBound)
      (b₁ + b₂) :=
  ⟨κ, gM, hM, gEM, hEM, a₁, b₁, a₂, b₂, h₁, h₂, hE, hA, le_rfl, le_rfl⟩

/-- **Potential running time of a relabelled costed simulator**: that of its simulator, at an
import of the events that the relabelling does not increase and an import of the outputs that
it does not increase. -/
theorem mapPorts.timeBoundPot_timed {T : Simulator.Timed EM OM EG OG U W} {gM : EM → ℕ}
    {gO : OG → ℕ} {hEG : EG → ℕ} {hM : OM → ℕ} {a b : ℕ}
    (hT : T.TimeBoundPot gM gO hEG hM a b) (f : E → EM) (g : OM → O) {gE : E → ℕ} {hO : O → ℕ}
    (hf : ∀ e, gM (f e) ≤ gE e) (hg : ∀ o, hO (g o) ≤ hM o) :
    (Simulator.Timed.mapPorts T f g : Simulator.Timed E O EG OG V W).TimeBoundPot gE gO hEG hO
      a b :=
  ⟨gM, hM, hf, hg, hT⟩

/-- **Potential running time of the costed tensor**: if `πT` and `π'T` erase to `π` and `π'` and
have potential time bounds with constants `a`, `b` and `a'`, `b'`, the costed tensor has the
potential time bound with the imports of the components on the two sides, the constants
`max a a' + 7`, `max b b'` and the sum of the potentials. -/
theorem tensor.timeBoundPot_timed {π : MultiHybrid σ E O EG OG}
    {π' : MultiHybrid σ' E' O' EG' OG'} {πT : MultiHybrid.Timed σ E O EG OG}
    {π'T : MultiHybrid.Timed σ' E' O' EG' OG'} {gE : E → ℕ} {gO : OG → ℕ} {hEG : EG → ℕ}
    {hO : O → ℕ} {gE' : E' → ℕ} {gO' : OG' → ℕ} {hEG' : EG' → ℕ} {hO' : O' → ℕ}
    {a b a' b' : ℕ} (hE : πT.Erases π) (hE' : π'T.Erases π')
    (P : πT.PotentialBound gE gO hEG hO a b) (P' : π'T.PotentialBound gE' gO' hEG' hO' a' b') :
    (tensor.timed (V := V) (W := W) (V' := V') (W' := W') π π' πT π'T).TimeBoundPot
      (Sum.elim gE gE') (Sum.elim gO gO') (Sum.elim hEG hEG') (Sum.elim hO hO') (max a a' + 7)
      (max b b') := by
  obtain ⟨_, _, _, rfl⟩ := hE
  obtain ⟨_, _, _, rfl⟩ := hE'
  exact ofMultiHybrid.timeBoundPot_timed (MultiHybrid.Timed.PotentialBound.tensor _ _ rfl rfl P P')

/-- A costed simulator at other views has the inner events per activation of the costed
simulator. -/
theorem mono.calls (T : Simulator.Timed E O EG OG V W) (V' : PubView E O) (W' : PubView EG OG) :
    (T.mono V' W').calls = T.calls := by
  induction T with
  | ofMultiHybrid πT => rfl
  | ofMultiHybridHat εσ εE εO εEG εOG πT => rfl
  | comp T₁ T₂ ih₁ ih₂ => simp only [Simulator.Timed.mono, Simulator.Timed.calls, ih₁, ih₂]
  | mapPorts T f g ih => simp only [Simulator.Timed.mono, Simulator.Timed.calls, ih]

/-- A costed simulator at other views passes the messages across its inner interfaces per
activation of the costed simulator. -/
theorem mono.msgBound (T : Simulator.Timed E O EG OG V W) (V' : PubView E O)
    (W' : PubView EG OG) : (T.mono V' W').msgBound = T.msgBound := by
  induction T with
  | ofMultiHybrid πT => rfl
  | ofMultiHybridHat εσ εE εO εEG εOG πT => rfl
  | comp T₁ T₂ ih₁ ih₂ =>
    simp only [Simulator.Timed.mono, Simulator.Timed.msgBound, mono.calls, ih₁, ih₂]
  | mapPorts T f g ih => simp only [Simulator.Timed.mono, Simulator.Timed.msgBound, ih]

/-- **Potential running time of a costed simulator at other views**: the potential time bound
of the costed simulator. -/
theorem mono.timeBoundPot_timed {T : Simulator.Timed E O EG OG V W} {gE : E → ℕ}
    {gO : OG → ℕ} {hEG : EG → ℕ} {hO : O → ℕ} {a b : ℕ} (hT : T.TimeBoundPot gE gO hEG hO a b)
    (V' : PubView E O) (W' : PubView EG OG) :
    (T.mono V' W').TimeBoundPot gE gO hEG hO a b := by
  induction T generalizing a b with
  | ofMultiHybrid πT => exact hT
  | ofMultiHybridHat εσ εE εO εEG εOG πT => exact hT
  | comp T₁ T₂ ih₁ ih₂ =>
    obtain ⟨κ, gM, hM, gEM, hEM, a₁, b₁, a₂, b₂, h₁, h₂, hE, hA, h3, h4⟩ := hT
    refine ⟨κ, gM, hM, gEM, hEM, a₁, b₁, a₂, b₂, ih₁ h₁ _ _, ih₂ h₂ _ _, hE, hA, ?_, h4⟩
    simp only [Simulator.Timed.msgBound] at h3 ⊢
    simpa only [mono.calls, mono.msgBound] using h3
  | mapPorts T f g ih =>
    obtain ⟨gM, hM, hf, hg, h⟩ := hT
    exact ⟨gM, hM, hf, hg, ih h _ _⟩

end Simulator

namespace Hybrid.Timed

variable {σ E O EG OG : Type}

/-- The potential time bound of a costed one-call hybrid machine, with the import `gE` of the
outer events and `gO` of the answers it receives, the import `hEG` of the inner events and `hO`
of the outer outputs it passes on, and the constants `a`, `b`: an invariant `Inv` and a potential
`Φ` on the states, with `Inv` at the initial state, such that a `pre` step on `e` from a state
`s` of `Inv` costs at most `a + b * (Φ s + gE e)` and returns states `s'` of `Inv` with inner
events `g` where `Φ s' + hEG g ≤ Φ s + gE e`, and likewise a `post` step on `o` with `gO o` and
the import `hO` of its outputs. -/
structure PotentialBound (A : Hybrid.Timed σ E O EG OG) (gE : E → ℕ) (gO : OG → ℕ)
    (hEG : EG → ℕ) (hO : O → ℕ) (a b : ℕ) where
  /-- The invariant on the states. -/
  Inv : σ → Prop
  /-- The potential of a state. -/
  Φ : σ → ℕ
  /-- The initial state satisfies the invariant. -/
  init : Inv A.init
  /-- The time and the potential clause of a `pre` step. -/
  pre : ∀ s e, Inv s →
    SPTree.Timed.stepTime (A.preCost s e, A.pre s e) ≤ a + b * (Φ s + gE e) ∧
    SPTree.Timed.AllRet (fun y => Inv y.1 ∧ Φ y.1 + hEG y.2 ≤ Φ s + gE e) (A.pre s e)
  /-- The time and the potential clause of a `post` step. -/
  post : ∀ s o, Inv s →
    SPTree.Timed.stepTime (A.postCost s o, A.post s o) ≤ a + b * (Φ s + gO o) ∧
    SPTree.Timed.AllRet (fun y => Inv y.1 ∧ Φ y.1 + hO y.2 ≤ Φ s + gO o) (A.post s o)

variable {A : Hybrid.Timed σ E O EG OG} {gE : E → ℕ} {gO : OG → ℕ} {hEG : EG → ℕ}
  {hO : O → ℕ} {a b : ℕ}

namespace PotentialBound

/-- **A step bound linear in the import is a potential time bound** with the potential `0`: if a
`pre` step on `e` costs at most `a + b * gE e` and passes on inner events of import at most
`gE e`, and a `post` step on `o` costs at most `a + b * gO o` and passes on outputs of import at
most `gO o`, the costed one-call hybrid machine has the potential time bound `a`, `b` on every
state. -/
def ofStepBound
    (hpre : ∀ s e, SPTree.Timed.stepTime (A.preCost s e, A.pre s e) ≤ a + b * gE e ∧
      SPTree.Timed.AllRet (fun y => hEG y.2 ≤ gE e) (A.pre s e))
    (hpost : ∀ s o, SPTree.Timed.stepTime (A.postCost s o, A.post s o) ≤ a + b * gO o ∧
      SPTree.Timed.AllRet (fun y => hO y.2 ≤ gO o) (A.post s o)) :
    A.PotentialBound gE gO hEG hO a b where
  Inv _ := True
  Φ _ := 0
  init := trivial
  pre s e _ := ⟨by simpa only [Nat.zero_add] using (hpre s e).1,
    SPTree.Timed.allRet_mono (fun _ hy => ⟨trivial, by simpa only [Nat.zero_add] using hy⟩) _
      (hpre s e).2⟩
  post s o _ := ⟨by simpa only [Nat.zero_add] using (hpost s o).1,
    SPTree.Timed.allRet_mono (fun _ hy => ⟨trivial, by simpa only [Nat.zero_add] using hy⟩) _
      (hpost s o).2⟩

/-- **Conservation through a wrapped hybrid machine**: let `A'` run the `pre` steps of `A` at
an extra cost `c`, and as a `post` step on `o` the `post` step of `A` followed by a continuation
`k s o` at an extra cost `c`. If the continuation on an output `y` of a state of the invariant
costs at most `a' + b' * hO y.2` and passes on an output whose import together with the
potential is at most `Φ y.1 + hO y.2`, then `A'` has the potential time bound with the constants
`a + a' + c` and `b + b'` and the potential of `A`: the import `A` passes on to the continuation
is bounded by the potential clause of `A`. -/
def wrapPost {O' : Type} {A' : Hybrid.Timed σ E O' EG OG} {hO' : O' → ℕ} {a' b' c : ℕ}
    (P : A.PotentialBound gE gO hEG hO a b) (hinit : A'.init = A.init)
    (hpre : ∀ s e, SPTree.Timed.stepTime (A'.preCost s e, A'.pre s e) ≤
        c + SPTree.Timed.stepTime (A.preCost s e, A.pre s e) ∧
      ∀ Q, SPTree.Timed.AllRet Q (A.pre s e) → SPTree.Timed.AllRet Q (A'.pre s e))
    (k : σ → OG → σ × O → ℕ × SPTree.Timed (σ × O'))
    (hpost : ∀ s o, SPTree.Timed.stepTime (A'.postCost s o, A'.post s o) ≤
        c + A.postCost s o + SPTree.Timed.stepTime ((A.post s o).bind (k s o)) ∧
      ∀ Q, SPTree.Timed.AllRet Q ((A.post s o).bind (k s o)).2 →
        SPTree.Timed.AllRet Q (A'.post s o))
    (hk : ∀ s o y, P.Inv y.1 → SPTree.Timed.stepTime (k s o y) ≤ a' + b' * hO y.2 ∧
      SPTree.Timed.AllRet (fun z => P.Inv z.1 ∧ P.Φ z.1 + hO' z.2 ≤ P.Φ y.1 + hO y.2)
        (k s o y).2) :
    A'.PotentialBound gE gO hEG hO' (a + a' + c) (b + b') where
  Inv := P.Inv
  Φ := P.Φ
  init := hinit ▸ P.init
  pre s e hs := by
    refine ⟨?_, (hpre s e).2 _ (P.pre s e hs).2⟩
    have := (hpre s e).1
    have := (P.pre s e hs).1
    have := Nat.add_mul b b' (P.Φ s + gE e)
    omega
  post s o hs := by
    obtain ⟨ht, hr⟩ := P.post s o hs
    refine ⟨?_, (hpost s o).2 _ ((SPTree.Timed.allRet_bind _ _ _).2
      (SPTree.Timed.allRet_mono (fun y hy => SPTree.Timed.allRet_mono
        (fun z hz => ⟨hz.1, by omega⟩) _ (hk s o y hy.1).2) _ hr))⟩
    have hb := SPTree.Timed.stepTime_bind_le_of_allRet (A.post s o) (k s o)
      (a' + b' * (P.Φ s + gO o)) hr fun y hy => le_trans (hk s o y hy.1).1
        (Nat.add_le_add_left (Nat.mul_le_mul_left b' (by omega)) a')
    have h1 := (hpost s o).1
    have := Nat.add_mul b b' (P.Φ s + gO o)
    simp only [SPTree.Timed.stepTime] at ht hb h1 ⊢
    omega

end PotentialBound

/-- The costed one-call multi-call hybrid of the costed hybrid machine `A`: the costed form
`MultiHybrid.ofHybrid.timed π` with the steps and cost companions of `A`. -/
noncomputable def ofHybrid (π : Hybrid σ E O EG OG) (A : Hybrid.Timed σ E O EG OG) :
    MultiHybrid.Timed σ E O EG OG :=
  MultiHybrid.ofHybrid.timed π A.pre A.preCost A.post A.postCost

/-- **Erasure of the costed one-call multi-call hybrid**: the costed one-call multi-call hybrid
of a costed hybrid machine that erases to `π` erases to `MultiHybrid.ofHybrid π`. -/
theorem ofHybrid_erases {π : Hybrid σ E O EG OG} (hA : A.Erases π) :
    (ofHybrid π A).Erases (MultiHybrid.ofHybrid π) := by
  obtain ⟨_, _, rfl⟩ := hA
  exact MultiHybrid.ofHybrid.erase_timed _ _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)

/-- **Potential running time of the costed one-call multi-call hybrid**: a potential time bound
of a costed hybrid machine that erases to `π` is a potential time bound of its costed one-call
multi-call hybrid, with the same potential and the constant `a + 1`. -/
def PotentialBound.ofHybrid {π : Hybrid σ E O EG OG} (hA : A.Erases π)
    (P : A.PotentialBound gE gO hEG hO a b) :
    (ofHybrid π A).PotentialBound gE gO hEG hO (a + 1) b where
  Inv := P.Inv
  Φ := P.Φ
  init := by
    obtain ⟨_, _, rfl⟩ := hA
    exact P.init
  start s e hs := by
    obtain ⟨ht, hr⟩ := P.pre s e hs
    have hb := SPTree.Timed.stepTime_bind_le (A.pre s e)
      (fun x => (0, SPTree.Timed.ret (x.1, (Sum.inl x.2 : EG ⊕ O)))) 0
      (fun _ => by simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret])
    refine ⟨?_, ?_⟩
    · simp only [Hybrid.Timed.ofHybrid, MultiHybrid.ofHybrid.timed,
        MultiHybrid.ofHybrid.start.tree.timed, SPTree.Timed.delay, SPTree.Timed.stepTime] at ht hb ⊢
      omega
    · simp only [Hybrid.Timed.ofHybrid, MultiHybrid.ofHybrid.timed,
        MultiHybrid.ofHybrid.start.tree.timed, SPTree.Timed.delay]
      exact (SPTree.Timed.allRet_bind _ _ _).2 (SPTree.Timed.allRet_mono (fun _ hy => hy) _ hr)
  resume s o hs := by
    obtain ⟨ht, hr⟩ := P.post s o hs
    have hb := SPTree.Timed.stepTime_bind_le (A.post s o)
      (fun x => (0, SPTree.Timed.ret (x.1, (Sum.inr x.2 : EG ⊕ O)))) 0
      (fun _ => by simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret])
    refine ⟨?_, ?_⟩
    · simp only [Hybrid.Timed.ofHybrid, MultiHybrid.ofHybrid.timed,
        MultiHybrid.ofHybrid.resume.tree.timed, SPTree.Timed.delay,
        SPTree.Timed.stepTime] at ht hb ⊢
      omega
    · simp only [Hybrid.Timed.ofHybrid, MultiHybrid.ofHybrid.timed,
        MultiHybrid.ofHybrid.resume.tree.timed, SPTree.Timed.delay]
      exact (SPTree.Timed.allRet_bind _ _ _).2 (SPTree.Timed.allRet_mono (fun _ hy => hy) _ hr)
  finish s o hs := by
    obtain ⟨ht, hr⟩ := P.post s o hs
    refine ⟨?_, hr⟩
    simp only [Hybrid.Timed.ofHybrid, MultiHybrid.ofHybrid.timed,
      MultiHybrid.ofHybrid.finish.tree.timed, SPTree.Timed.stepTime] at ht ⊢
    omega

end Hybrid.Timed

end CatCrypt.Crypto.UCTransparent
